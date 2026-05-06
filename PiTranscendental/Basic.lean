import Batteries.Tactic.Init
import Mathlib.Algebra.Algebra.Equiv
import Mathlib.Algebra.Algebra.Rat
import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Defs
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.Notation
import Mathlib.Data.Multiset.Powerset
import Mathlib.Data.Nat.Prime.Int
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import Mathlib.RingTheory.MvPolynomial.Symmetric.NewtonIdentities
import Mathlib.RingTheory.Polynomial.Vieta

open scoped Polynomial
open Complex (I)

def Complex.IsRat (x : ℂ) := ∃ val : ℚ, x = ↑val

lemma polynomial_of_roots (roots : Multiset ℂ) :
    (∑ k ∈ Finset.range (roots.card + 1),
      (-1)^k * (Polynomial.monomial (roots.card - k)) (roots.esymm k)
    ).roots = roots
    := by
  rw [
    Finset.sum_congr
    (g := fun j ↦ (-1) ^ j * (Polynomial.C (roots.esymm j) * Polynomial.X ^ (roots.card - j)))
    (by rfl) ?eq
  ]
  case eq =>
    intro x hx
    simp
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  rw [← Multiset.prod_X_sub_X_eq_sum_esymm]
  exact Polynomial.roots_multiset_prod_X_sub_C roots

theorem List.map_sublistsLen {α β : Type*} {m : ℕ} {l : List α} {f : α → β} :
    (l.sublistsLen m).map (List.map f) = (l.map f).sublistsLen m := by
  induction l generalizing m with
  | nil =>
    cases m <;> rfl
  | cons a l ih =>
    cases m with
    | zero => rfl
    | succ m =>
      simp [List.map_cons, List.sublistsLen_succ_cons, List.map_append]
      congr
      · exact ih
      · rw [← ih]
        simp

theorem Multiset.map_coe' {α β : Type*} (f : α → β) :
    Multiset.map f ∘ Multiset.ofList = Multiset.ofList ∘ List.map f  := by
  ext; simp
theorem Multiset.sum_coe' {M : Type*} [AddCommMonoid M] :
    Multiset.sum (M :=M) ∘ Multiset.ofList = List.sum (α :=M) := by
  ext; simp

theorem MvPolynomial.X_sum_injective {R σ : Type*} [CommSemiring R] [Nontrivial R] [DecidableEq σ] :
    Function.Injective (fun (x : Finset σ) => ∑ a ∈ x, X (R :=R) a) := by
  simp [Function.Injective]
  intro s t h
  rw [Finset.ext_iff]
  contrapose! h
  obtain ⟨i, hi⟩ := h
  wlog! hi : i ∈ s ∧ i ∉ t; grind
  apply ne_of_apply_ne (lcoeff _ (Finsupp.single i 1))
  simp [hi]

noncomputable def list_subsum_polys
    (R : Type*) [CommSemiring R] (n m : ℕ) : List (MvPolynomial (Fin n) R) := 
  List.ofFn MvPolynomial.X |>.sublistsLen m |>.map List.sum
lemma sublist_sum_eq_subsum_polys_eval
    (R : Type*) {S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (l : List S) (m : ℕ) :
      (l.sublistsLen m).map List.sum = (list_subsum_polys R _ m).map (MvPolynomial.aeval l.get)
    := by
  simp [list_subsum_polys]
  conv in (_ ∘ _) =>
    conv => 
      ext x; simp; rw [map_list_sum]
    rw [← Function.comp_def]
  rw [← List.map_map, List.map_sublistsLen, List.map_ofFn, Function.comp_def]
  simp
lemma list_subsum_polys_as_multiset
    (R : Type*) [CommSemiring R] (n m : ℕ) :
      Multiset.ofList (list_subsum_polys R n m)
        = (Finset.powersetCard m Finset.univ).val.map (fun x ↦ ∑ a ∈ x, MvPolynomial.X a) := by
  unfold list_subsum_polys
  simp [List.ofFn_eq_map, ← List.map_sublistsLen]
  rw [← Multiset.map_coe, ← Multiset.sum_coe', Function.comp_assoc, ← Multiset.map_coe']
  rw [← Function.comp_assoc, ← Multiset.map_map, Multiset.map_coe, ← Multiset.powersetCard_coe]
  simp [← Finset.val_univ_fin, ← Finset.map_val_val_powersetCard]

lemma list_esymm
    (R : Type*) {S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S] (l : List S) (k : ℕ) :
      (Multiset.ofList l).esymm k = (MvPolynomial.esymm (Fin l.length) R k).aeval l.get
    := by
  simp [MvPolynomial.aeval_esymm_eq_multiset_esymm]

lemma List.getElem_map' {α β : Type*} (f : α → β) (l : List α) : (l.map f).get = (f l[·]) := by
  ext
  simp

lemma aeval_comp_aeval {σ τ R S : Type*} [CommSemiring R] [CommSemiring S] [Algebra R S]
    (polys : σ → MvPolynomial τ R) (params : τ → S) (q : MvPolynomial σ R) :
    (MvPolynomial.aeval (fun (s : σ) => MvPolynomial.aeval params (polys s)) q)
      = (MvPolynomial.aeval params (MvPolynomial.aeval polys q))
    := by
  let f : MvPolynomial σ R →ₐ[R] S
    := MvPolynomial.aeval (fun s ↦ MvPolynomial.aeval params (polys s))
  let g : MvPolynomial σ R →ₐ[R] S
    := (MvPolynomial.aeval params).comp (MvPolynomial.aeval polys)
  have : f = g := by
    ext q
    simp [f, g]
  trans f q
  · simp [f]
  rw [this]
  simp [g]

def IsInvariantFamily {σ τ R : Type*} [CommSemiring R] (polys : σ → MvPolynomial τ R) : Prop :=
  ∀ perm_τ : Equiv.Perm τ, ∃ perm_σ : Equiv.Perm σ, ∀ s : σ,
  (polys s).rename perm_τ = (polys (perm_σ s))
lemma symmetric_composition {σ τ R : Type*} [CommSemiring R]
    (polys : σ → MvPolynomial τ R) (polys_symmetric : IsInvariantFamily polys)
    (q : MvPolynomial σ R) (hq : q.IsSymmetric) :
      q.aeval polys |>.IsSymmetric := by
  simp [MvPolynomial.IsSymmetric]
  intro e
  rw [← AlgHom.comp_apply]
  rw [show
    (MvPolynomial.rename ⇑e).comp (MvPolynomial.aeval polys)
    = MvPolynomial.aeval (fun s => MvPolynomial.rename ⇑e (polys s))
    from by ext; simp]
  obtain ⟨π, hπ⟩ := polys_symmetric e
  conv in ((MvPolynomial.rename _) _) => rw [hπ]
  rw [show (fun s => polys (π s)) = (polys ∘ π) from by ext; simp]
  rw [← MvPolynomial.aeval_rename, hq]

lemma list_equiv_perm_if_bij
    {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    {f : α → α} (hf : Set.BijOn f {x | x ∈ l} {x | x ∈ l})
    {len : ℕ} (hlen : len = l.length) :
      ∃ perm : Equiv.Perm (Fin len), ∀ i : Fin len, (l.map f)[i]'(by grind) = l[perm i] := by
  subst hlen
  use hl.getEquiv |>.trans (Set.BijOn.equiv f hf) |>.trans hl.getEquiv.symm
  intro i
  simp
  rfl

lemma list_subsum_polys_is_invariant
    {R : Type*} [CommSemiring R] [DecidableEq R] [Nontrivial R] (n m : ℕ)
    {len : ℕ} (h_len : len = (list_subsum_polys R n m).length) :
      IsInvariantFamily (fun (i : Fin len) => (list_subsum_polys R n m)[i]) := by
  dsimp [IsInvariantFamily]
  intro perm_τ
  conv in (MvPolynomial.rename _) _ =>
    rw [← List.getElem_map (MvPolynomial.rename _) (h := by grind)]
  apply list_equiv_perm_if_bij ?nodup ?bij (by grind)
  case nodup =>
    rw [← Multiset.coe_nodup, list_subsum_polys_as_multiset]
    rw [Finset.nodup_map_iff_injOn]
    apply Set.injOn_of_injective
    apply MvPolynomial.X_sum_injective
  case bij =>
    let s := {x | x ∈ list_subsum_polys R n m}
    have (perm_τ : Equiv.Perm (Fin n)) :
        Set.MapsTo (MvPolynomial.renameEquiv _ perm_τ).toEquiv s s := by
      simp [s, Set.MapsTo]
      simp [← Multiset.mem_coe]
      rw [list_subsum_polys_as_multiset]
      simp
      intro p hp
      use p.map perm_τ
      simp
      tauto
    rw [show MvPolynomial.rename perm_τ = MvPolynomial.renameEquiv R perm_τ
        from by ext1 f; symm; apply MvPolynomial.renameEquiv_apply]
    apply Equiv.bijOn'
    · apply this
    · apply this

lemma aeval_IsRat
    {σ : Type*} {p : MvPolynomial σ ℚ} {params : σ → ℂ} (hp : ∀ s : σ, (params s).IsRat) :
      p.aeval params |>.IsRat := by
  choose v hv using hp
  use MvPolynomial.aeval v p
  let ratToComplexAlg : ℚ →ₐ[ℚ] ℂ := Algebra.ofId ℚ ℂ
  have : MvPolynomial.aeval params = ratToComplexAlg.comp (MvPolynomial.aeval v) := by
    ext x
    simp
    exact hv x
  rw [this]
  simp

lemma symmetric_aeval
    {σ : Type*} [Fintype σ] (p : MvPolynomial σ ℚ) (hp : p.IsSymmetric) (params : σ → ℂ)
    (hparams : ∀ n : ℕ, Finset.univ (α := σ) |>.val.map params |>.esymm n |>.IsRat) :
      p.aeval params |>.IsRat := by
  let f := (MvPolynomial.esymmAlgEquiv σ ℚ (Eq.refl (Fintype.card σ)))
  let p' : ↥(MvPolynomial.symmetricSubalgebra σ ℚ) :=
    ⟨p, MvPolynomial.mem_symmetricSubalgebra p |>.mpr hp⟩
  rw [show p = f (f.symm p') from by simp; rfl]
  conv in f => unfold f
  simp
  rw [MvPolynomial.esymmAlgHom_apply, ← aeval_comp_aeval]
  apply aeval_IsRat
  intro s
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm]
  grind

lemma list_esymm_rat (l : List ℂ) (m k : ℕ) (hparams : ∀ n : ℕ, (Multiset.ofList l).esymm n |>.IsRat) :
    Complex.IsRat (Multiset.esymm (l.sublistsLen m |>.map List.sum) k) := by
  rw [sublist_sum_eq_subsum_polys_eval ℚ, list_esymm ℚ, List.getElem_map', aeval_comp_aeval]
  apply symmetric_aeval
  · apply symmetric_composition
    · exact list_subsum_polys_is_invariant (R := ℚ) _ _ (by grind)
    · apply MvPolynomial.esymm_isSymmetric
  · simp
    assumption

lemma Multiset.esymm_zero_if_gt
    {R : Type*} (s : Multiset R) [CommSemiring R] {n : ℕ} (h : s.card < n) : s.esymm n = 0 := by
  simp [esymm, powersetCard_eq_empty _ h]
lemma Multiset.esymm_empty
    {R : Type*} [CommSemiring R] (n : ℕ) : esymm (0 : Multiset R) n = if n = 0 then 1 else 0 := by
  cases n with
  | zero => simp [esymm]
  | succ n => simp [esymm_zero_if_gt]

lemma aroots_esymm_israt {p : ℤ[X]} (k : ℕ) : ((p.aroots ℂ).esymm k).IsRat := by
  by_cases! hp : p = 0
  · simp [hp, Multiset.esymm_empty, Complex.IsRat]
    by_cases k = 0
    · use 1; simp; tauto
    · use 0; simp; tauto
  obtain hp' := Polynomial.leadingCoeff_ne_zero.mpr hp
  rw [Polynomial.aroots_def]
  set p' := Polynomial.map (algebraMap ℤ ℂ) p
  have hroots := IsAlgClosed.card_roots_eq_natDegree (p := p')
  set n := p'.natDegree with hn
  by_cases! h : n < k
  · rw [Multiset.esymm_zero_if_gt]
    · use 0; simp
    · rw [hroots]; tauto
  rw [show k = n - (n - k) from by grind]
  have hesymm := Polynomial.coeff_eq_esymm_roots_of_card hroots (show n - k ≤ n from by grind)
  rw [← hn] at hesymm
  have reducer {a b c d : ℂ} {ha : a.IsRat} {hb : b.IsRat} {hc : c.IsRat} {hb0 : b ≠ 0} {hc0 : c ≠ 0}
      (h : a = b * c * d) : d.IsRat := by
    obtain ⟨a', ha'⟩ := ha
    obtain ⟨b', hb'⟩ := hb
    obtain ⟨c', hc'⟩ := hc
    use a' / b' / c'
    simp [← ha', ← hb', ← hc', h]
    grind
  apply reducer at hesymm
  · tauto
  · simp [p', Complex.IsRat]; use p.coeff (n-k); simp
  · simp [p', Complex.IsRat]
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    · simp; use p.leadingCoeff; simp
    · simp; grind
  · use (-1) ^ (n - (n - k)); simp
  · rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    · simp; grind
    · simp; grind
  · apply pow_ne_zero
    grind

-- This probably has better proof using ring theory
lemma zpoly_aroots_exists_if_qpoly_exists (roots : Multiset ℂ) (hq : ∃ q : ℚ[X], q.aroots ℂ = roots) : 
    ∃ p : ℤ[X], p.aroots ℂ = roots := by
  obtain ⟨q, hq⟩ := hq
  by_cases hq0 : q = 0
  · use 0
    simp [hq0] at hq ⊢
    tauto
  let p' := q * q.coeffs.lcm Rat.den
  have h_den : ∀ n, (p'.coeff n).den = 1 := by 
    intro n
    simp [p']
    rw [← Rat.num_div_den (q.coeff n)]
    have (a : ℤ) (b c : ℕ) : (a : ℚ) / (b : ℚ) * (c : ℚ) = (((a*c) : ℤ) : ℚ) / ((b : ℤ) : ℚ) := by simp; grind
    rw [this, Rat.den_div_intCast_eq_one_iff _ _ (by simp)]
    apply Int.dvd_mul_of_dvd_right
    rw [Int.ofNat_dvd]
    by_cases h0 : q.coeff n = 0; simp [h0]
    apply Finset.dvd_lcm 
    apply Polynomial.coeff_mem_coeffs h0
  let p : ℤ[X] := p'.sum (fun n c => Polynomial.monomial n c.num)
  have hqz : p.map (algebraMap ℤ ℚ) = p' := by 
    ext i
    simp [p]
    simp [Polynomial.coeff_monomial, Polynomial.sum_def]
    by_cases h : p'.coeff i = 0; simp [h]
    simp [h]
    grind [Rat.coe_int_num_of_den_eq_one]
  use p
  simp [Polynomial.aroots] at ⊢ hq
  rw [
    show Int.castRingHom ℂ = (algebraMap ℚ ℂ).comp (algebraMap ℤ ℚ)
    from by rw [← algebraMap_int_eq, ← Algebra.compHom_algebraMap_eq]; rfl,
    ← Polynomial.map_map,
    hqz,
  ]
  simp [p']
  rw [Polynomial.roots_mul ?nz, ← Polynomial.C_eq_natCast, Polynomial.roots_C]
  grind
  case nz =>
    apply mul_ne_zero
    · contrapose! hq0
      rw [Polynomial.map_eq_zero] at hq0
      tauto
    · simp

noncomputable def θ_roots (p : ℤ[X]) (m : ℕ) : Multiset ℂ
  := p.aroots ℂ |>.powersetCard m |>.map Multiset.sum

lemma θ_coeff_rat (p : ℤ[X]) (m k : ℕ) : θ_roots p m |>.esymm k |>.IsRat := by
  simp [θ_roots]
  rw [← Multiset.coe_toList (p.aroots ℂ), Multiset.powersetCard_coe]
  simp
  simp [show Multiset.sum ∘ Multiset.ofList = List.sum from by ext; rfl]
  apply list_esymm_rat (p.aroots ℂ).toList m k
  simp
  exact aroots_esymm_israt

lemma θ_exists (p : ℤ[X]) (m : ℕ) : ∃ q : ℤ[X], q.aroots ℂ = θ_roots p m := by
  apply zpoly_aroots_exists_if_qpoly_exists
  use ∑ k ∈ Finset.range ((θ_roots p m).card + 1),
    (-1)^k * Polynomial.monomial ((θ_roots p m).card - k) (Classical.choose (θ_coeff_rat p m k))
  simp [Polynomial.aroots, Polynomial.map_sum]
  conv =>
    lhs; rhs; rhs; ext k; rhs;
    rw [← Classical.choose_spec (θ_coeff_rat p m k)]
  exact polynomial_of_roots _

lemma prod_roots (s : Multiset ℤ[X]) (hs : ∀ p ∈ s, p ≠ 0) :
    s.prod.aroots ℂ = (s.map (Polynomial.aroots · ℂ)).join := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    simp
    rw [Polynomial.aroots_mul]
    · grind
    · rw [← Multiset.prod_cons]
      apply Multiset.prod_ne_zero
      grind

theorem polynomial_of_sums (p : ℤ[X]) (hp : p ≠ 0) :
    ∃ q : ℤ[X], q.aroots ℂ = (p.aroots ℂ |>.powerset |>.map Multiset.sum) := by
  rw [← Multiset.bind_powerset_len]
  generalize hn : (p.aroots ℂ).card + 1 = n
  simp [Multiset.bind, Multiset.map_join]
  conv in Multiset.map _ =>
    rhs
    change θ_roots p
  use (Multiset.range n).map (fun m ↦ Classical.choose (θ_exists p m)) |>.prod
  rw [prod_roots]
  simp
  · conv in (fun _ => Polynomial.aroots _ _) =>
      ext m
      rw [Classical.choose_spec (θ_exists p m)]
  · intro p' hp'
    contrapose hp'
    rw [hp']
    simp
    intro m hm
    contrapose hp
    have : (Classical.choose (θ_exists p m)).aroots ℂ = 0 := by simp [hp]
    rw [Classical.choose_spec (θ_exists p m)] at this
    contrapose! this
    simp [θ_roots]
    intro h
    apply congr_arg Multiset.card at h
    simp at h
    rw [Nat.choose_eq_zero_iff] at h
    grind

lemma polynomial_without_zero (p : ℤ[X]) : ∃ q : ℤ[X], q.aroots ℂ = (p.aroots ℂ).filter (· ≠ 0) := by
  by_cases! hp : p = 0
  · use 0; simp [hp]
  have h := Polynomial.pow_mul_divByMonic_rootMultiplicity_eq p 0
  simp at h
  set xn := Polynomial.X (R :=ℤ) ^ p.rootMultiplicity 0
  use p /ₘ xn
  rw [← Multiset.add_right_inj (s := xn.aroots ℂ), ← Polynomial.aroots_mul (by grind), h]
  have : xn.aroots ℂ = (p.aroots ℂ).filter (· = 0) := by
    simp [xn]
    rw [← Polynomial.count_roots]
    ext x
    by_cases! h : x ≠ 0; simp [h]
    simp [h]
    rw [show (0 : ℂ) = Int.castRingHom ℂ 0 from by simp]
    apply Polynomial.eq_rootMultiplicity_map Int.cast_injective
  rw [this, Multiset.filter_add_not]

lemma θ_construction (p : ℤ[X]) (hp : p ≠ 0) : ∃ q : ℤ[X],
    q.aroots ℂ = (p.aroots ℂ |>.powerset |>.map Multiset.sum |>.filter (· ≠ 0)) := by
  obtain ⟨q', hq'⟩ := polynomial_of_sums p hp
  obtain ⟨q, hq⟩ := polynomial_without_zero q'
  use q
  grind

variable {h : IsAlgebraic ℤ (Real.pi * I)}
noncomputable def poly_witness := Classical.choose h
lemma poly_witness_spec :
    @poly_witness h ≠ 0 ∧ (Polynomial.aeval (Real.pi * I) : ℤ[X] → ℂ) (@poly_witness h) = 0 := by
  simp [poly_witness]
  grind

noncomputable def βs' := (@poly_witness h).aroots ℂ |>.powerset |>.map Multiset.sum
noncomputable def βs := @βs' h |>.filter (· ≠ 0)

noncomputable def θ :=
  θ_construction poly_witness (Classical.choose_spec h).left |> Classical.choose
lemma θ_spec : (@θ h).aroots ℂ = @βs h := by
  simp [θ, βs, βs']
  grind

noncomputable def c := (@θ h).leadingCoeff 
noncomputable def r := (@θ h).natDegree
noncomputable def cᵣ := (@θ h).coeff 0
variable {p : ℕ}
noncomputable def s := (@r h) * p - 1
noncomputable def f := Polynomial.C ((@c h)^(@s h p)) * (Polynomial.X^(p-1) * (@θ h)^p)
noncomputable def F :=
  ∑ i ∈ Finset.Icc 0 ((@s h p) + p), Polynomial.derivative^[i] (@f h p)
noncomputable def k := (@βs' h).count 0


lemma r_ge_one : 1 ≤ @r h := by
  simp [r]
  by_contra hn
  simp at hn
  rw [← IsAlgClosed.card_aroots_eq_natDegree (B := ℂ)] at hn
  obtain hθ := @θ_spec h
  obtain hp := @poly_witness_spec h
  rw [← Polynomial.mem_aroots, ← Multiset.singleton_le, ← Multiset.mem_powerset] at hp
  apply Multiset.mem_map_of_mem (f := Multiset.sum) at hp
  conv at hp => rhs; simp
  apply Multiset.mem_filter_of_mem (p := (· ≠ 0)) at hp
  obtain hp := hp (by simp)
  unfold βs βs' at hθ
  rw [← hθ] at hp
  have : 0 < (@θ h |>.aroots ℂ).card := by
    rw [Multiset.card_pos_iff_exists_mem]
    use Real.pi * I
  grind
lemma θ_ne_zero : @θ h ≠ 0 := by
  have := @r_ge_one h
  simp [r] at this
  exact Polynomial.ne_zero_of_natDegree_gt this
lemma k_pos : 0 < @k h := by
  simp [k, βs', Multiset.count_pos]
  use ∅
  simp
lemma cᵣ_ne_zero : @cᵣ h ≠ 0 := by
  have := @θ_spec h
  simp [βs] at this
  have : 0 ∉ (@θ h).aroots ℂ := by rw [this]; simp
  rw [Polynomial.mem_aroots] at this
  simp [θ_ne_zero, ← Polynomial.coeff_zero_eq_aeval_zero'] at this
  simp [cᵣ]
  tauto

-- Should definitely be in mathlib!
attribute [local fun_prop] Polynomial.differentiableAt_aeval
attribute [local fun_prop] Polynomial.continuous_aeval  


lemma deriv_ex_fx (hp : 0 < p) :
    deriv (fun x ↦ Complex.exp (-x) * (@F h p).aeval x)
      = (fun x ↦ -(Complex.exp (-x) * (@f h p).aeval x)) := by
  ext x
  simp [F]
  rw [deriv_fun_mul ?a ?b, deriv_cexp ?c, deriv_fun_sum ?d]
  case a | b | c | d => intros; fun_prop
  rw [mul_assoc, ← mul_add]
  conv => rhs; rw [← mul_neg]
  congr
  simp
  conv =>
    lhs; rhs; rhs; ext i; rhs
    rw [← Function.comp_apply (f :=Polynomial.derivative), ← Function.iterate_succ']
  rw [← Finset.sum_image (f := fun i ↦ (Polynomial.derivative)^[i] f |>.aeval x) (g := Nat.succ) ?inj]
  case inj => 
    apply Set.injOn_of_injective
    exact Nat.succ_injective
  simp [show Nat.succ = (· + 1) from by simp, Finset.image_add_right_Icc]
  rw [← Finset.insert_Icc_add_one_left_eq_Icc (by simp)]
  rw [← Finset.insert_Icc_right_eq_Icc_add_one (by simp)]
  simp
  ring_nf
  rw [add_eq_left]
  convert Polynomial.aeval_zero _
  apply Polynomial.iterate_derivative_eq_zero
  --
  guard_target = f.natDegree < 1 + s + p
  --
  unfold f
  rw [Polynomial.natDegree_C_mul (by simp [c]; grind [θ_ne_zero])]
  rw [Polynomial.natDegree_X_pow_mul _ (by simp; grind [θ_ne_zero])]
  simp
  rw [show θ.natDegree = @r h from by simp [r]]
  unfold s
  grind

lemma equation_20 (hp : 0 < p) (x : ℂ) :
    (@F h p).aeval x - Complex.exp x * (@F h p).aeval 0
      = -x * ∫ (t : ℝ) in 0..1, Complex.exp ((1-t)*x) * (@f h p).aeval (t * x) := by
  apply mul_left_cancel₀ (show Complex.exp (-x) ≠ 0 from Complex.exp_ne_zero (-x))
  let G (x : ℂ) := Complex.exp (-x) * (@F h p).aeval x
  let g (x : ℂ) := -Complex.exp (-x) * (@f h p).aeval x
  trans G (0+x) - G 0
  · simp [G]; simp [mul_sub, ← mul_assoc]; simp [Complex.exp_neg]
  have : IsScalarTower ℝ ℂ ℂ := inferInstance
  have h_int : _ = G (0 + x) - G 0 :=   -- Why do I need to explicitly specify the instance????
    @intervalIntegral.integral_unitInterval_deriv_eq_sub ℂ ℂ _ _ _ _ _ this _ g _ _ ?hcont ?hderiv
  rw [← h_int]
  simp [g]
  conv => lhs; rhs; arg 1; ext t
  conv =>
    rhs; rhs; rhs; arg 1; ext t
    simp [sub_mul]
    simp [sub_eq_add_neg, Complex.exp_add]
    rw [mul_assoc]
  rw [← mul_assoc, mul_comm (Complex.exp (-x)), Complex.exp_neg]
  simp [← smul_eq_mul]
  case hcont => simp; fun_prop
  case hderiv =>
    have : deriv G = g := by
      simp [g, G]
      apply deriv_ex_fx hp
    rw [← this]
    intro t ht
    apply DifferentiableAt.hasDerivAt
    fun_prop [G]

lemma Multiset.prod_add_one {R : Type*} [CommSemiring R] (s : Multiset R) :
    (s.map (1 + ·)).prod = (s.powerset.map Multiset.prod).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    simp [ih, Multiset.sum_map_mul_left]
    ring_nf

lemma Multiset.map_map_powerset {α β : Type*} (s : Multiset α) (f : α → β) :
    s.powerset.map (Multiset.map f) = (s.map f).powerset := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons p s ih =>
    simp [ih]
    rw [show (fun x => f p ::ₘ map f x) = (cons (f p)) ∘ map f from by ext; simp]
    rw [← Multiset.map_map]
    grind

lemma exp_sum_is_int : -(@βs h |>.map Complex.exp |>.sum) = (@k h : ℂ) := by
  simp [k]
  rw [neg_eq_iff_add_eq_zero]
  have := Multiset.sum_map_eq_nsmul_single
    (m := (@βs' h).filter (· = 0)) (f := (fun x => Complex.exp x)) 0 ?cond
  case cond => intro i hi hs; simp [hi] at hs
  conv at this => rhs; simp
  rw [← this, ← Multiset.sum_add, ← Multiset.map_add, Multiset.add_comm]
  simp [βs, Multiset.filter_add_not, βs']
  have : (fun x => Complex.exp x.sum) = Multiset.prod ∘ (Multiset.map Complex.exp) := by
    ext x; simp
    exact Complex.exp_multiset_sum x
  rw [this, ← Multiset.map_map, Multiset.map_map_powerset, ← Multiset.prod_add_one]
  rw [Multiset.map_map]
  apply Multiset.prod_eq_zero
  rw [show 0 = ((1 + ·) ∘ Complex.exp) (Real.pi * I) from by simp]
  apply Multiset.mem_map_of_mem
  obtain hp := @poly_witness_spec h
  rw [← Polynomial.mem_aroots] at hp
  grind

noncomputable def lhs := ((@βs h).map (fun β ↦ (@F h p).aeval β)).sum + @k h * (@F h p).aeval 0
noncomputable def rhs := 
  -((@βs h).map
      (fun β ↦ β * ∫ (t : ℝ) in 0..1, Complex.exp ((1-t)*β) * (@f h p).aeval (t * β))
  ).sum

lemma equation_21 : ∀ᶠp in Filter.atTop, @lhs h p = @rhs h p := by
  rw [Filter.eventually_atTop]
  use 1
  intro p hp

  unfold lhs rhs
  have := congr_arg (fun f ↦ ((@βs h).map f).sum) (funext (@equation_20 h p hp))
  simp at this
  rename_bvar i → β at this
  rw [← this, sub_eq_add_neg, Multiset.sum_map_mul_right]
  simp [← exp_sum_is_int]

lemma iterate_derivative_mul_of_root
    (p q : ℤ[X]) (a : ℂ) (n m : ℕ) (ha : q.aeval a = 0) (hm : n < m) :
      (Polynomial.derivative^[n] (p * q^m)).aeval a = 0 := by
  rw [← Polynomial.eval_map_algebraMap] at *
  rw [← Polynomial.iterate_derivative_map, Polynomial.map_mul, Polynomial.map_pow]
  set q' := Polynomial.map (algebraMap ℤ ℂ) q
  rw [← Polynomial.IsRoot.def, ← Polynomial.dvd_iff_isRoot] at ha
  obtain ⟨r, hr⟩ := ha
  rw [mul_comm] at hr
  rw [hr, mul_pow, ← mul_assoc, Polynomial.iterate_derivative_mul, Polynomial.eval_finset_sum]
  apply Finset.sum_eq_zero
  intro x hx; simp; right; right
  rw [Polynomial.iterate_derivative_X_sub_pow]
  simp; grind

lemma Multiset.ofList_ofFn_eq_self {α : Type*} (s : Multiset α) :
    Multiset.map s.toList.get Finset.univ.val = s := by
  change ↑(List.map s.toList.get (List.finRange s.toList.length)) = s
  rw [← List.ofFn_eq_map, List.ofFn_get, Multiset.coe_toList]

lemma multiset_psum_eq_mvpoly_psum (s : Multiset ℂ) (k : ℕ) :
    (s.map (·^k)).sum = (MvPolynomial.psum (Fin s.toList.length) ℤ k).aeval s.toList.get := by
  simp [MvPolynomial.psum]
  nth_rw 1 [← Multiset.coe_toList s]
  rw [Multiset.map_coe, Multiset.sum_coe]
  nth_rw 1 [← List.ofFn_get s.toList]
  rw [List.map_ofFn, List.sum_ofFn]
  simp

lemma Multiset.roots_esymm_eq_coeff_div_leadingCoeff
    {p : ℤ[X]} (hp : p ≠ 0) {k : ℕ} (hk : k ≤ p.natDegree) :
      (p.aroots ℂ).esymm k = p.coeff (p.natDegree - k) * (-1) ^ k / p.leadingCoeff := by
  simp [Polynomial.aroots]
  set q := p.map (Int.castRingHom ℂ)
  have h_natDegree : p.natDegree = q.natDegree := by
    symm
    simp [q, hp]
  have h_coeff : p.coeff (p.natDegree - k) = q.coeff (q.natDegree - k) := by
    rw [← h_natDegree]
    simp [q]
  have h_leadingCoeff : p.leadingCoeff = q.leadingCoeff := by
    simp [q]
    rw [Polynomial.leadingCoeff_map_of_leadingCoeff_ne_zero]
    simp
    simp [hp]
  have := Polynomial.coeff_eq_esymm_roots_of_card (p := q) ?hroots (k := q.natDegree - k) ?hk
  case hroots => apply IsAlgClosed.card_roots_eq_natDegree
  case hk => simp [q]
  rw [h_coeff, h_leadingCoeff, this]
  rw [show q.natDegree - (q.natDegree - k) = k from by grind]
  ring_nf
  have : q.leadingCoeff ≠ 0 := by
    simp [q]
    rw [Polynomial.map_eq_zero_iff]
    grind
    simp [Function.Injective]
  rw [mul_comm q.leadingCoeff, mul_inv_cancel_right₀ this]
  rw [pow_mul' (-1) k 2]
  simp

lemma Multiset.esymm_of_gt_card_zero
    {R : Type*} [CommSemiring R] {s : Multiset R} {k : ℕ} (hk : s.card < k) : s.esymm k = 0 := by
  simp [Multiset.esymm]
  rw [Multiset.powersetCard_eq_empty _ (by grind)]
  simp


def IsIntDivPow (x : ℂ) (z : ℤ) (k : ℕ) := ∃ m : ℤ, m = x * z ^ k 
lemma IsIntDivPow_weak {x : ℂ} {z : ℤ} (hz : z ≠ 0) {k l : ℕ} (hx : IsIntDivPow x z k) (hl : k ≤ l) :
    IsIntDivPow x z l := by
  obtain ⟨a, ha⟩ := hx
  use a * z ^ (l - k)
  simp [ha]
  rw [pow_sub₀ _ _ hl, mul_comm (_ ^ l), ← mul_assoc, mul_inv_cancel_right₀]
  ring_nf
  all_goals (simp; grind)
lemma IsIntDivPow_add {x y : ℂ} {z : ℤ} {k : ℕ} (hx : IsIntDivPow x z k) (hy : IsIntDivPow y z k) :
    IsIntDivPow (x+y) z k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a + b
  simp [ha, hb]
  rw [add_mul]
lemma IsIntDivPow_sub {x y : ℂ} {z : ℤ} {k : ℕ} (hx : IsIntDivPow x z k) (hy : IsIntDivPow y z k) :
    IsIntDivPow (x - y) z k := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a - b
  simp [ha, hb]
  rw [sub_mul]
lemma IsIntDivPow_mul
    {x y : ℂ} {z : ℤ} {k l m : ℕ}
    (hx : IsIntDivPow x z k) (hy : IsIntDivPow y z l) (hm : k + l = m) :
      IsIntDivPow (x * y) z m := by
  obtain ⟨a, ha⟩ := hx
  obtain ⟨b, hb⟩ := hy
  use a * b
  simp [ha, hb]
  grind
lemma IsIntDivPow_sum
    {z : ℤ} {ι : Type} {s : Finset ι} {f : ι → ℂ} {k : ℕ} (h : ∀ i ∈ s, IsIntDivPow (f i) z k) :
      IsIntDivPow (s.sum f) z k := by
  choose a ha using h
  use ∑ i ∈ s.attach, a i.val i.prop
  simp
  rw [Finset.sum_mul, ← Finset.sum_attach s]
  apply Finset.sum_congr (by rfl) (by grind)
lemma IsIntDivPow_esymm {p : ℤ[X]} (hp : p ≠ 0) (k : ℕ) :
    IsIntDivPow (
      (MvPolynomial.aeval (p.aroots ℂ).toList.get)
      (MvPolynomial.esymm (Fin (p.aroots ℂ).toList.length) ℤ k)
    ) p.leadingCoeff 1 := by
  rw [MvPolynomial.aeval_esymm_eq_multiset_esymm, Multiset.ofList_ofFn_eq_self]
  by_cases! h : k ≤ p.natDegree
  · rw [Multiset.roots_esymm_eq_coeff_div_leadingCoeff (by simp; grind) (by grind)]
    use p.coeff (p.natDegree - k) * (-1) ^ k
    simp
    rw [div_mul_cancel₀ _ (by simp; grind)]
  · use 0; simp; left
    apply Multiset.esymm_of_gt_card_zero
    rw [IsAlgClosed.card_roots_eq_natDegree]
    convert h
    apply Polynomial.natDegree_map_of_leadingCoeff_ne_zero
    simp
    grind

lemma roots_psum_eq_int_div_leadingCoeff_pow {p : ℤ[X]} (hp : p ≠ 0) (k : ℕ) :
    IsIntDivPow (p.aroots ℂ |>.map (·^k) |>.sum) p.leadingCoeff k := by
  rw [multiset_psum_eq_mvpoly_psum]
  induction k using Nat.strong_induction_on; case h k h =>
  by_cases! hk : k = 0
  · use (p.aroots ℂ).card; simp [hk]
  rw [MvPolynomial.psum_eq_mul_esymm_sub_sum _ _ _ (by grind)]
  simp
  have : p.leadingCoeff ≠ 0 := by simp; tauto
  apply IsIntDivPow_sub
  · apply IsIntDivPow_mul _ _ (show 0 + k = k from by omega)
    · use (-1)^(k+1) * k; simp
    · apply IsIntDivPow_weak this _ (show 1 ≤ k from by omega)
      apply IsIntDivPow_esymm hp
  · apply IsIntDivPow_sum
    intro ⟨i, j⟩ hi
    simp at hi ⊢
    rw [mul_assoc]
    apply IsIntDivPow_mul _ _ (show 0 + k = k from by omega)
    · use (-1)^i; simp
    · apply IsIntDivPow_mul _ _ (show 1 + (k - 1) = k from by omega)
      · apply IsIntDivPow_esymm hp
      · apply IsIntDivPow_weak this _ (show j ≤ k - 1 from by omega)
        apply h j (by omega)

lemma lhs_prop : ∀ᶠ p in Filter.atTop, p.Prime →
    ∃ m : ℤ, @lhs h p = m * (p-1).factorial ∧ ¬ (p : ℤ) ∣ m := by
  rw [Filter.eventually_atTop]
  use max (max (@k h) (@c h).natAbs) (@cᵣ h).natAbs + 2
  intro p hpb hpp

  simp [lhs, F]
  simp [← Polynomial.coeff_zero_eq_aeval_zero']
  rw [Multiset.sum_map_sum, ← Finset.Ico_add_one_right_eq_Icc]
  rw [← Finset.sum_Ico_consecutive _ (n := p) (by omega) (by omega)]
  rw [← Int.cast_sum]

  have (a b : ℂ) (c : ℤ) (ha : a = 0) (hb : ∃ m : ℤ, b = m * p.factorial)
      (hc : ∃ m : ℤ, c = m * (p-1).factorial ∧ ¬ (p : ℤ) ∣ m) :
      ∃ m : ℤ, a + b + @k h * c = m * (p-1).factorial ∧ ¬ (p : ℤ) ∣ m := by
    obtain ⟨b', hb'⟩ := hb
    obtain ⟨c', hc', hc''⟩ := hc
    simp [ha, hb', hc']
    rw [← Nat.mul_factorial_pred (by omega)]
    use b' * p + @k h * c'
    constructor
    · simp
      ring_nf
    · rw [Int.dvd_mul_self_add]
      simp [← Int.natAbs_dvd_natAbs, Int.natAbs_mul]
      apply Nat.Prime.not_dvd_mul hpp
      · rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.coprime_of_lt_prime (by grind [k_pos]) (by omega) hpp
      · simp [← Int.natAbs_dvd_natAbs] at hc''
        tauto
  apply this
  all_goals clear this

  · unfold f
    simp only [Polynomial.iterate_derivative_C_mul]
    convert Finset.sum_const_zero with i hi; simp at hi
    convert Multiset.sum_map_zero with β hβ
    simp; right
    rw [iterate_derivative_mul_of_root (hm := by omega)]
    rw [← θ_spec] at hβ
    rw [Polynomial.mem_aroots] at hβ
    tauto

  · unfold f
    simp only [Polynomial.iterate_derivative_C_mul]
    rw [← Finset.sum_attach]

    have (p : ℤ[X]) (hp : p ≠ 0) {k l : ℕ} (hk : l ≤ k) :
        IsIntDivPow (p.aroots ℂ |>.map (·^l) |>.sum) p.leadingCoeff k := by
      apply IsIntDivPow_weak (by simp; tauto) _ hk
      apply roots_psum_eq_int_div_leadingCoeff_pow hp
    choose g hg using this

    have (n k : ℕ) (hk : p ≤ k) : p.factorial ∣ n.descFactorial k := by
      trans k.factorial
      exact Nat.factorial_dvd_factorial hk
      exact Nat.factorial_dvd_descFactorial n k
    choose g2 hg2 using this

    conv =>
      enter [1, m, 1, 2, i]
      conv =>
        enter [1, 1, β]
        rw [Polynomial.as_sum_range_C_mul_X_pow (_ ^ _ * _ ^ _)]
        rw [Polynomial.iterate_derivative_sum]
        simp [Polynomial.iterate_derivative_X_pow_eq_C_mul]
        rw [Finset.mul_sum, ← Finset.sum_attach]
      simp [Multiset.sum_map_sum]
      conv =>
        enter [2, j]
        repeat rw [Multiset.sum_map_mul_left]
        unfold c
        rw [mul_comm, mul_assoc, mul_assoc, ← θ_spec, ← hg _ θ_ne_zero]
        rw [hg2 _ _ (by obtain ⟨i, hi⟩ := i; simp at hi; tauto)]
        rfl
        tactic =>
          guard_target = j.val - i.val ≤ s
          obtain ⟨i, hi⟩ := i; simp at hi
          obtain ⟨j, hj⟩ := j; simp at hj
          rw [Polynomial.natDegree_X_pow_mul _ (by simp; grind [θ_ne_zero])] at hj
          simp at hj
          rw [show θ.natDegree = @r h from by simp [r]] at hj
          simp
          trans p * @r h + (p - 1); omega
          trans @s h p + p; unfold s; grind
          omega
    simp
    have {ι κ : Type 0} (s : Finset ι) (t : Finset κ) (a b c : ι → κ → ℤ) :
        ∃ m : ℤ, ∑ i ∈ s, ∑ j ∈ t, (a i j : ℂ) * (p.factorial * b i j * c i j) = m * p.factorial := by
      use ∑ i ∈ s, ∑ j ∈ t, a i j * b i j * c i j
      simp
      simp [Finset.sum_mul]
      apply Finset.sum_congr (by rfl); intros
      apply Finset.sum_congr (by rfl); intros
      ring_nf
    apply this

  · unfold f
    simp only [Polynomial.iterate_derivative_C_mul, Polynomial.coeff_C_mul]
    simp [Polynomial.coeff_iterate_derivative, Nat.descFactorial_self]
    simp [Polynomial.coeff_X_pow_mul', ← Finset.sum_filter]
    rw [Finset.sum_congr
      (show _ = (Finset.range (@s h p + p + 1)).filter (fun i => p - 1 ≤ i) from by ext; simp)
      (by intros; rfl)]
    rw [← Nat.Ico_zero_eq_range, Finset.Ico_filter_le]
    simp
    rw [Finset.sum_eq_sum_Ico_succ_bot (by omega), show p - 1 + 1 = p by omega]
    simp
    rw [← Polynomial.constantCoeff_apply, RingHom.map_pow]
    simp
    rw [show (@θ h).coeff 0 = @cᵣ h by simp [cᵣ], mul_comm _ (_ ^ _), ← mul_assoc]
    rw [← Finset.sum_attach]
    conv =>
      enter [1, m, 1, 1, 2, 2, i]
      rw [← Nat.factorial_mul_descFactorial (k := i - p) (by simp)]
      rw [Nat.sub_sub_self (by obtain ⟨i, hi⟩ := i; simp at hi ⊢; omega)]
      rw [mul_comm p.factorial, mul_comm _ (Polynomial.coeff _ _)]
      simp
      rw [← mul_assoc, ← mul_assoc]
    rw [← Finset.sum_mul]
    have (a b : ℤ) (h : ¬ (p : ℤ) ∣ a) :
        ∃ m : ℤ, a * (p-1).factorial + b * p.factorial = m * (p-1).factorial ∧ ¬ (p : ℤ) ∣ m := by
      use a + b * p
      constructor
      · rw [← Nat.mul_factorial_pred (show p ≠ 0 by omega)]
        simp; ring_nf
      · contrapose h
        exact Int.dvd_add_mul_self.mp h
    apply this
    have hp : Prime (p : ℤ) := by exact Nat.prime_iff_prime_int.mp hpp
    apply Prime.not_dvd_mul hp
    · rw [Prime.dvd_pow_iff_dvd hp]
      · simp [← Int.natAbs_dvd_natAbs]
        rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.coprime_of_lt_prime ?_ (by omega) hpp
        simp [c]
        apply θ_ne_zero
      · unfold s
        apply Nat.sub_ne_zero_of_lt
        have := @r_ge_one h
        rw [Nat.one_lt_mul_iff]
        omega
    · rw [Prime.dvd_pow_iff_dvd hp]
      · simp [← Int.natAbs_dvd_natAbs]
        rw [← Nat.Prime.coprime_iff_not_dvd hpp]
        apply Nat.coprime_of_lt_prime ?_ (by omega) hpp
        simp
        apply cᵣ_ne_zero
      · omega

lemma lhs_prop_abs (z : ℂ) (p : ℕ) (h : ∃ m : ℤ, z = m * (p - 1).factorial ∧ ¬ (p : ℤ) ∣ m) :
    1 ≤ ‖z / (p-1).factorial‖ := by
  obtain ⟨m, hz, hm⟩ := h
  rw [hz]
  simp
  rw [mul_div_cancel_right₀ _ (by simp; apply Nat.factorial_ne_zero)]
  suffices 1 ≤ |m| from by norm_cast
  apply Int.one_le_abs
  contrapose hm
  simp [hm]

lemma rhs_convergence_lemma (a b : ℝ) :
    Filter.Tendsto (fun (n : ℕ) => a * b ^ (n-1) / (n-1).factorial) Filter.atTop (nhds 0) := by
  conv => enter [1, n]; rw [mul_div_assoc]
  rw [show 0 = a * 0 from by simp]
  apply Filter.Tendsto.const_mul
  apply Filter.Tendsto.comp (f := (· - 1)) (g := fun (n : ℕ) ↦ b^n / n.factorial)
  · apply FloorSemiring.tendsto_pow_div_factorial_atTop
  · apply Filter.tendsto_sub_atTop_nat

lemma rhs_prop : Filter.Tendsto (fun p ↦ @rhs h p / (p-1).factorial) Filter.atTop (nhds 0) := by
  simp [rhs, f]
  apply squeeze_zero_norm
  · intro p
    rewrite [neg_div, norm_neg, ← Multiset.sum_map_div]
    apply norm_multiset_sum_le
  simp
  conv in nhds _ => rw [show (0 : ℝ) = (@βs h |>.map (fun _ => 0) |>.sum) from by simp]
  apply tendsto_multiset_sum
  intro β hβ
  conv => enter [1, p]; rw [← mul_div]
  conv in nhds _ => rw [show (0 : ℝ) = ‖β‖ * 0 from by simp]
  apply Filter.Tendsto.const_mul
  apply squeeze_zero_norm'
  · simp
    use 1
    intro p hp

    set r := @r h with hr
    have hr₁ : 1 ≤ r := by grind [r_ge_one]
    apply le_trans  -- Prevent `conv` from closing the goal
    conv =>
      enter [1, 1, 1, 1, t]
      equals ((1-t)*β).exp * @c h ^ (r-1) * (@θ h).aeval (t*β)
          * (@c h^r * t*β * (@θ h).aeval (t*β))^(p-1) =>
        simp [s, ← hr]
        have : r * p - 1 = r - 1 + r * (p - 1) := by
          have : 1 ≤ r * p := Right.one_le_mul hr₁ hp
          zify [hr₁, hp, this]
          ring_nf
        rw [this, pow_add, ← mul_pow_sub_one (show p ≠ 0 from by omega)]
        ring_nf

    rewrite [div_le_div_iff_of_pos_right (by positivity)]
    apply le_trans
    · apply intervalIntegral.norm_integral_le_integral_norm (by simp)
    · simp
      apply intervalIntegral.integral_mono_on (by simp)
      case' hf | hg => apply Continuous.intervalIntegrable
      case' h =>
        intro t ht
        have {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : a ≤ c) (hd : b ≤ d) : a * b ≤ c * d := by
          trans c * b
          · exact mul_le_mul_of_nonneg_right hc hb
          · apply mul_le_mul_of_nonneg_left hd
            apply ha.trans hc
        apply this (by positivity) (by positivity)
        case' hd => apply pow_le_pow_left₀ (by positivity)
        all_goals (
          apply ContinuousOn.le_sSup_image_Icc (hc := ht)
          apply Continuous.continuousOn
        )
      all_goals apply_rules [Continuous.mul, Continuous.pow] <;> try continuity
      all_goals (
        apply Continuous.comp (by continuity)
        apply Continuous.comp (g := fun u ↦ (Polynomial.aeval u) θ)
        all_goals continuity
      )
  conv => enter [1, p]; simp
  apply rhs_convergence_lemma

theorem pi_transcendental : Transcendental ℤ Real.pi := by
  simp [Transcendental]
  by_contra that
  apply IsAlgebraic.algebraMap (A := ℂ) at that
  simp at that

  have: IsAlgebraic ℤ I := by
    use Polynomial.X^2 + 1; simp
    rw [Polynomial.ext_iff]
    simp; use 0; simp
  have h := IsAlgebraic.mul that this

  have rhs_prop := Metric.tendsto_nhds.mp (@rhs_prop h) 1 (by simp)
  have infinite_primes := Filter.frequently_atTop.mpr Nat.exists_infinite_primes
  have := @equation_21 h |>.and (@lhs_prop h) |>.and rhs_prop
  obtain ⟨p, hp, ⟨he, hl⟩, hr⟩ := infinite_primes.and_eventually this |>.exists
  specialize hl hp
  apply lhs_prop_abs at hl
  simp [he] at hl hr
  linarith

#print axioms pi_transcendental
