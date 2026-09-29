-- Prove2me | solution 1 for MilnorConjecture.galoisSymbol_steinberg
-- status  : ACCEPTED   (prove)
-- author  : @vatsj
-- created : 2026-09-29T01:17:18.548659+00:00
-- url     : https://prove2.me/submissions/d507fe3d-c4f5-44aa-b3ce-de4080a94bf3

import Mathlib
import Definitions.Def_MilnorConjecture_MilnorK
import Definitions.Def_MilnorConjecture_GaloisSymbol

/-!
# The Steinberg relation for the Galois symbol

If two adjacent entries of `a : Fin n → Fˣ` satisfy `aᵢ + aᵢ₊₁ = 1`, then `galoisSymbol a = 0`.

Route (all at the level of the mission's homogeneous cochains):

1. `classOf` of the coboundary of an invariant continuous cochain is `0`.
2. A Leibniz rule for multiplying by a two-variable cochain.
3. Tate's cochain: for `p + q = 1`, a continuous `ψ : G_F → ℤ/2` with
   `ψ(στ) = ψ(σ) + ψ(τ) + χ_p(σ) χ_q(τ)`, built from `γ` with `γ² = 1 - √q`.
4. By induction on the position of the pair, the symbol cochain is the coboundary of an
   explicit invariant continuous cochain.

The homological plumbing in the first section (`uncurryN`, `curryN_injective`, `classOf_spec`
and the `TopModuleCat` lemmas) is taken from Lucas's accepted proof of
`MilnorConjecture.norm_residue_ker_le_of_le_one` on Prove2Me.
-/

open CategoryTheory Limits

namespace MilnorConjecture

section Plumbing

universe u

variable {k G M : Type u} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M] [Module k M]
  [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M]

/-- `v ↦ (v₀, tail v)`. (From Lucas's proof.) -/
def unconsMap (n : ℕ) : C(Fin (n + 1) → G, G × (Fin n → G)) :=
  ⟨fun v ↦ (v 0, Fin.tail v), by unfold Fin.tail; fun_prop⟩

variable (k G M) in
/-- Inverse of `curryN`. (From Lucas's proof.) -/
noncomputable def uncurryN : (n : ℕ) →
    C(((trivialRep k G M).resolutionX n : Type u), C(Fin n → G, M))
  | 0 => ⟨fun m ↦ ContinuousMap.const _ m, ContinuousMap.continuous_const'⟩
  | n + 1 => ⟨fun φ ↦ (ContinuousMap.uncurry ((uncurryN n).comp φ)).comp (unconsMap n),
      (ContinuousMap.continuous_precomp _).comp
        (ContinuousMap.continuous_uncurry.comp (ContinuousMap.continuous_postcomp _))⟩

@[simp] lemma uncurryN_succ_apply {n : ℕ} (φ : ((trivialRep k G M).resolutionX (n + 1) : Type u))
    (v : Fin (n + 1) → G) :
    uncurryN k G M (n + 1) φ v = uncurryN k G M n (φ (v 0)) (Fin.tail v) := rfl

lemma uncurryN_curryN (n : ℕ) (F : C(Fin n → G, M)) :
    uncurryN k G M n (curryN k G M n F) = F := by
  induction n with
  | zero =>
    ext v
    show F Fin.elim0 = F v
    exact congrArg F (funext fun i ↦ i.elim0)
  | succ n ih =>
    ext v
    rw [uncurryN_succ_apply, curryN_succ_apply, ih]
    show F (Fin.cons (v 0) (Fin.tail v)) = F v
    rw [Fin.cons_self_tail]

lemma curryN_injective (n : ℕ) : Function.Injective (curryN k G M n) :=
  Function.LeftInverse.injective (uncurryN_curryN (k := k) n)

variable [IsTopologicalRing k]

lemma TopModuleCat_injective_of_mono {X Y : TopModuleCat.{u} k} (f : X ⟶ Y) [Mono f] :
    Function.Injective f := by
  intro x y hxy
  let ix : TopModuleCat.of k k ⟶ X := TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k x)
  let iy : TopModuleCat.of k k ⟶ X := TopModuleCat.ofHom (ContinuousLinearMap.toSpanSingleton k y)
  have : ix ≫ f = iy ≫ f := by
    apply ConcreteCategory.ext
    apply ContinuousLinearMap.ext_ring
    rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply]
    change f ((1 : k) • x) = f ((1 : k) • y)
    rw [one_smul, one_smul, hxy]
  have h2 := (cancel_mono f).mp this
  have h3 := congrArg (fun φ : TopModuleCat.of k k ⟶ X ↦ φ (1 : k)) h2
  change (1 : k) • x = (1 : k) • y at h3
  rwa [one_smul, one_smul] at h3

omit [IsTopologicalRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] [AddCommGroup M] [Module k M] [TopologicalSpace M]
  [IsTopologicalAddGroup M] [ContinuousSMul k M] in
lemma iCycles_liftCycles_apply (C : CochainComplex (TopModuleCat.{u} k) ℕ) {A : TopModuleCat.{u} k}
    {i : ℕ} (ι : A ⟶ C.X i) (j : ℕ) (hj : (ComplexShape.up ℕ).next i = j)
    (hk : ι ≫ C.d i j = 0) (x : A) : C.iCycles i (C.liftCycles ι j hj hk x) = ι x := by
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.liftCycles_i]

lemma classOf_spec (n : ℕ) (F : C(Fin (n + 1) → G, M))
    (hinv : ∀ (g : G) (v : Fin (n + 1) → G), F (fun i ↦ g * v i) = F v)
    (hcoc : coboundary (n + 1) F = 0) :
    ∃ z : (trivialRep k G M).homogeneousCochains.cycles n,
      ((trivialRep k G M).homogeneousCochains.iCycles n z).1 = curryN k G M (n + 1) F ∧
      classOf k n F hinv hcoc = (trivialRep k G M).homogeneousCochains.homologyπ n z := by
  refine ⟨_, ?_, rfl⟩
  erw [iCycles_liftCycles_apply]
  change ((1 : k) • curryN k G M (n + 1) F) = _
  rw [one_smul]

/-- The class of the coboundary of an invariant continuous cochain vanishes. -/
lemma classOf_coboundary_eq_zero {n : ℕ} (F' : C(Fin (n + 1) → G, M))
    (hinv' : ∀ (g : G) (v : Fin (n + 1) → G), F' (fun i ↦ g * v i) = F' v)
    (hinv : ∀ (g : G) (v : Fin (n + 2) → G),
      coboundary (n + 1) F' (fun i ↦ g * v i) = coboundary (n + 1) F' v)
    (hcoc : coboundary (n + 2) (coboundary (n + 1) F') = 0) :
    classOf k (n + 1) (coboundary (n + 1) F') hinv hcoc = 0 := by
  set C := (trivialRep k G M).homogeneousCochains
  obtain ⟨z, hz, hcl⟩ := classOf_spec (k := k) (n + 1) (coboundary (n + 1) F') hinv hcoc
  let y : C.X n := ⟨curryN k G M (n + 1) F', curryN_mem_invariants F' hinv'⟩
  have hzy : z = C.toCycles n (n + 1) y := by
    apply TopModuleCat_injective_of_mono (C.iCycles (n + 1))
    rw [← ConcreteCategory.comp_apply (C.toCycles n (n + 1)), HomologicalComplex.toCycles_i]
    apply Subtype.ext
    rw [hz, TopRep.homogeneousCochains.d_apply]
    exact (d_curryN (n + 1) F').symm
  rw [hcl, hzy, ← ConcreteCategory.comp_apply, HomologicalComplex.toCycles_comp_homologyπ,
    TopModuleCat.hom_zero_apply]

end Plumbing

section Leibniz

variable {G R : Type*} [CommRing R]

/-- Leibniz rule for multiplying by a two-variable cochain `Ψ`:
`δ(Ψ ∪ ρ) = δΨ ∪ ρ - Ψ ∪ δρ`. -/
lemma fcob_mul_two {m : ℕ} (Ψ : G → G → R) (ρ : (Fin (m + 1) → G) → R) (y : Fin (m + 3) → G) :
    fcob (fun x : Fin (m + 2) → G ↦ Ψ (x 0) (x 1) * ρ (Fin.tail x)) y =
      (Ψ (y 1) (y 2) - Ψ (y 0) (y 2) + Ψ (y 0) (y 1)) * ρ (Fin.tail (Fin.tail y)) -
        Ψ (y 0) (y 1) * fcob ρ (Fin.tail y) := by
  simp only [fcob]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, Fin.sum_univ_succ (n := m + 1)]
  have h0 : ∀ j : Fin (m + 1), (y ∘ j.succ.succ.succAbove) 0 = y 0 := fun j ↦ by simp
  have h1 : ∀ j : Fin (m + 1), (y ∘ j.succ.succ.succAbove) 1 = y 1 := fun j ↦ by
    rw [Function.comp_apply, ← Fin.succ_zero_eq_one, Fin.succ_succAbove_succ,
      Fin.succ_succAbove_zero, Fin.succ_zero_eq_one]
  have hT : ∀ j : Fin (m + 1),
      Fin.tail (y ∘ j.succ.succ.succAbove) = Fin.tail y ∘ j.succ.succAbove := fun j ↦ by
    funext i
    simp only [Fin.tail, Function.comp_apply, Fin.succ_succAbove_succ]
  have a1 : (Fin.succ 0 : Fin (m + 3)).succAbove 1 = 2 := by
    rw [show (1 : Fin (m + 2)) = Fin.succ 0 from rfl, Fin.succ_succAbove_succ]; rfl
  have a2 : Fin.tail (y ∘ (Fin.succ 0 : Fin (m + 3)).succAbove) = Fin.tail (Fin.tail y) := by
    funext i
    simp only [Fin.tail, Function.comp_apply, Fin.succ_succAbove_succ, Fin.succAbove_zero]
  have a3 : Fin.tail (y ∘ Fin.succ) = Fin.tail (Fin.tail y) := rfl
  have a4 : Fin.tail y ∘ Fin.succ = Fin.tail (Fin.tail y) := rfl
  have a5 : (y ∘ Fin.succ) 1 = y 2 := by rw [Function.comp_apply, Fin.succ_one_eq_two]
  have a6 : (y ∘ Fin.succ) 0 = y 1 := by rw [Function.comp_apply, Fin.succ_zero_eq_one]
  have a7 : (y ∘ (Fin.succ 0 : Fin (m + 3)).succAbove) 1 = y 2 := by rw [Function.comp_apply, a1]
  have a8 : (y ∘ (Fin.succ 0 : Fin (m + 3)).succAbove) 0 = y 0 := by simp
  simp only [h0, h1, hT, a2, a3, a5, a6, a7, a8, Fin.succAbove_zero, a4]
  have hs : ∑ j : Fin (m + 1), (-1 : R) ^ (j.succ.succ : ℕ) *
        (Ψ (y 0) (y 1) * ρ (Fin.tail y ∘ j.succ.succAbove)) =
      -(Ψ (y 0) (y 1) * ∑ j : Fin (m + 1), (-1 : R) ^ (j.succ : ℕ) *
        ρ (Fin.tail y ∘ j.succ.succAbove)) := by
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    simp only [Fin.val_succ]
    ring
  rw [hs]
  simp only [Fin.val_zero, Fin.val_succ, Fin.val_one, pow_zero, pow_one, zero_add, one_mul]
  ring

/-- Negation commutes with `fcob`. -/
lemma fcob_neg {m : ℕ} (f : (Fin m → G) → R) (y : Fin (m + 1) → G) :
    fcob (fun x ↦ -f x) y = -fcob f y := by
  simp [fcob, Finset.sum_neg_distrib]

variable [Group G] [TopologicalSpace G] [TopologicalSpace R] [IsTopologicalRing R]

/-- If the factors at positions `k` and `k + 1` of a product cochain are "cup-trivialised" by a
continuous invariant two-variable cochain `Ψ`, then the product cochain is the coboundary of a
continuous invariant cochain. -/
lemma exists_prodCochain_eq_fcob (k : ℕ) : ∀ (n : ℕ) (χ : Fin (n + 2) → G → R) (hk : k < n + 1)
    (Ψ : G → G → R)
    (hΨ : ∀ u v w, Ψ v w - Ψ u w + Ψ u v =
      (χ ⟨k, by omega⟩ v - χ ⟨k, by omega⟩ u) * (χ ⟨k + 1, by omega⟩ w - χ ⟨k + 1, by omega⟩ v))
    (hχc : ∀ l, Continuous (χ l))
    (hχinv : ∀ l (g x z : G), χ l (g * z) - χ l (g * x) = χ l z - χ l x)
    (hΨc : Continuous fun p : G × G ↦ Ψ p.1 p.2)
    (hΨinv : ∀ g u v, Ψ (g * u) (g * v) = Ψ u v),
    ∃ Θ : (Fin (n + 2) → G) → R, Continuous Θ ∧ (∀ g y, Θ (fun i ↦ g * y i) = Θ y) ∧
      ∀ y, prodCochain χ y = fcob Θ y := by
  induction k with
  | zero =>
    intro n χ _ Ψ hΨ hχc hχinv hΨc hΨinv
    refine ⟨fun y ↦ Ψ (y 0) (y 1) * prodCochain (Fin.tail (Fin.tail χ)) (Fin.tail y), ?_, ?_, ?_⟩
    · unfold prodCochain Fin.tail
      have := hχc
      have : Continuous fun y : Fin (n + 2) → G ↦ Ψ (y 0) (y 1) :=
        hΨc.comp (by fun_prop : Continuous fun y : Fin (n + 2) → G ↦ (y 0, y 1))
      fun_prop
    · intro g y
      simp only [prodCochain, Fin.tail, hΨinv, hχinv]
    · intro y
      rw [fcob_mul_two, fcob_prodCochain, mul_zero, sub_zero, hΨ, prodCochain_succ,
        prodCochain_succ, mul_assoc]
      rfl
  | succ k ih =>
    intro n χ hk Ψ hΨ hχc hχinv hΨc hΨinv
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨Θ, hΘc, hΘinv, hΘ⟩ := ih n (Fin.tail χ) (by omega) Ψ hΨ (fun l ↦ hχc _)
      (fun l ↦ hχinv _) hΨc hΨinv
    refine ⟨fun y ↦ -((χ 0 (y 1) - χ 0 (y 0)) * Θ (Fin.tail y)), ?_, ?_, ?_⟩
    · unfold Fin.tail
      have := hχc
      have : Continuous fun y : Fin (n + 3) → G ↦ Θ (fun i ↦ y i.succ) :=
        hΘc.comp (by fun_prop)
      fun_prop
    · intro g y
      simp only [Fin.tail, hχinv]
      congr 2
      exact hΘinv g _
    · intro y
      rw [fcob_neg, fcob_mul_tail, neg_neg, prodCochain_succ]
      congr 1
      exact hΘ _

end Leibniz

section Tate

variable {F : Type} [Field F] [NeZero (2 : F)]

local notation "K" => SeparableClosure F

lemma zmod2_cases (z : ZMod 2) : z = 0 ∨ z = 1 := by
  revert z; decide

/-- The sign `(-1)^z ∈ K` of `z : ℤ/2`. -/
noncomputable def sgn (z : ZMod 2) : K := if z = 0 then 1 else -1

lemma one_ne_neg_one_sep : (1 : K) ≠ -1 := by
  intro h
  have h2 : (2 : K) = 0 := by rw [← one_add_one_eq_two]; nth_rw 2 [h]; ring
  exact NeZero.ne ((2 : ℕ) : K) (by exact_mod_cast h2)

@[simp] lemma sgn_zero : sgn (F := F) 0 = 1 := rfl
@[simp] lemma sgn_one : sgn (F := F) 1 = -1 := rfl

lemma sgn_add (a b : ZMod 2) : sgn (F := F) (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp [show (1 : ZMod 2) + 1 = 0 from rfl]

lemma sgn_mul_self (a : ZMod 2) : sgn (F := F) a * sgn a = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp

lemma sgn_injective : Function.Injective (sgn (F := F)) := by
  intro a b h
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl <;>
    simp_all [one_ne_neg_one_sep, one_ne_neg_one_sep.symm]

lemma neg_ne_self_sep {β : K} (hβ : β ≠ 0) : -β ≠ β := by
  intro h
  have h2 : (2 : K) * β = 0 := by rw [two_mul]; nth_rw 1 [← h]; ring
  rcases mul_eq_zero.mp h2 with h2 | h2
  · exact NeZero.ne ((2 : ℕ) : K) (by exact_mod_cast h2)
  · exact hβ h2

lemma apply_sqrtSep_eq_sgn (u : Fˣ) (σ : AbsGal F) :
    σ (sqrtSep u) = sgn (kummerCharFun u σ) * sqrtSep u := by
  unfold kummerCharFun sgn
  by_cases h : σ (sqrtSep u) = sqrtSep u
  · simp [h]
  · have := (apply_sqrtSep u σ).resolve_left h
    simp [h, this]

variable (p q : Fˣ)

lemma one_sub_sqrtSep_ne_zero (hpq : (p : F) + q = 1) : 1 - sqrtSep q ≠ 0 := by
  intro h
  have h1 : sqrtSep q = 1 := by linear_combination -h
  have := sqrtSep_sq q
  rw [h1, one_pow, eq_comm, ← map_one (algebraMap F K), (algebraMap F K).injective.eq_iff] at this
  exact p.ne_zero (by linear_combination hpq - this)

lemma one_sub_mul_one_add (hpq : (p : F) + q = 1) :
    (1 - sqrtSep q) * (1 + sqrtSep q) = sqrtSep p ^ 2 := by
  have hq := sqrtSep_sq q
  rw [sqrtSep_sq, show (1 - sqrtSep q) * (1 + sqrtSep q) = 1 - sqrtSep q ^ 2 by ring, hq,
    ← map_one (algebraMap F K), ← map_sub, show (1 : F) - q = p by linear_combination -hpq]

/-- `γ` with `γ² = 1 - √q`. -/
noncomputable def tateGamma : K :=
  (IsSepClosed.exists_pow_nat_eq (1 - sqrtSep q) 2).choose

lemma tateGamma_sq : tateGamma q ^ 2 = 1 - sqrtSep q :=
  (IsSepClosed.exists_pow_nat_eq (1 - sqrtSep q) 2).choose_spec

open Classical in
/-- Tate's cochain: the sign of `σ γ` relative to `γ` (if `σ` fixes `√q`) or to `√p/γ`
(otherwise). -/
noncomputable def tatePsi (σ : AbsGal F) : ZMod 2 :=
  if σ (sqrtSep q) = sqrtSep q then (if σ (tateGamma q) = tateGamma q then 0 else 1)
  else (if tateGamma q * σ (tateGamma q) = sqrtSep p then 0 else 1)

/-- `B(σ) = γ` if `σ` fixes `√q`, and `√p/γ` otherwise. -/
noncomputable def tateB (σ : AbsGal F) : K :=
  if kummerCharFun q σ = 0 then tateGamma q else sqrtSep p * (tateGamma q)⁻¹

variable {p q}

lemma tateGamma_ne_zero (hpq : (p : F) + q = 1) : tateGamma q ≠ 0 := by
  intro h
  have := tateGamma_sq q
  rw [h, zero_pow two_ne_zero] at this
  exact one_sub_sqrtSep_ne_zero p q hpq this.symm

lemma apply_tateGamma (hpq : (p : F) + q = 1) (σ : AbsGal F) :
    σ (tateGamma q) = sgn (tatePsi p q σ) * tateB p q σ := by
  have hγ0 := tateGamma_ne_zero hpq
  have hσsq : (σ (tateGamma q)) ^ 2 = 1 - σ (sqrtSep q) := by
    rw [← map_pow, tateGamma_sq, map_sub, map_one]
  unfold tatePsi tateB
  by_cases hr : σ (sqrtSep q) = sqrtSep q
  · have hk : kummerCharFun q σ = 0 := by simp [kummerCharFun, hr]
    rw [if_pos hr, if_pos hk]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp (by rw [hσsq, hr, tateGamma_sq] :
        (σ (tateGamma q)) ^ 2 = tateGamma q ^ 2) with h | h
    · rw [if_pos h, sgn_zero, one_mul, h]
    · have hne : ¬ σ (tateGamma q) = tateGamma q := by rw [h]; exact neg_ne_self_sep hγ0
      rw [if_neg hne, sgn_one, neg_one_mul, h]
  · have hk : kummerCharFun q σ ≠ 0 := by simp [kummerCharFun, hr]
    have hr' := (apply_sqrtSep q σ).resolve_left hr
    rw [if_neg hr, if_neg hk]
    have key : (tateGamma q * σ (tateGamma q)) ^ 2 = sqrtSep p ^ 2 := by
      rw [mul_pow, tateGamma_sq, hσsq, hr', sub_neg_eq_add, one_sub_mul_one_add p q hpq]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp key with h | h
    · rw [if_pos h, sgn_zero, one_mul, ← h]
      field_simp
    · have hne : ¬ tateGamma q * σ (tateGamma q) = sqrtSep p := by
        rw [h]; exact neg_ne_self_sep (sqrtSep_ne_zero p)
      rw [if_neg hne, sgn_one, neg_one_mul, eq_neg_iff_add_eq_zero]
      field_simp
      linear_combination h

lemma sgn_ne_zero (z : ZMod 2) : sgn (F := F) z ≠ 0 := by
  rcases zmod2_cases z with rfl | rfl <;> simp

lemma map_sgn (σ : AbsGal F) (z : ZMod 2) : σ (sgn z) = sgn z := by
  rcases zmod2_cases z with rfl | rfl <;> simp

lemma tateB_ne_zero (hpq : (p : F) + q = 1) (σ : AbsGal F) : tateB p q σ ≠ 0 := by
  have := tateGamma_ne_zero hpq
  have := sqrtSep_ne_zero p
  unfold tateB; split_ifs <;> simp_all

lemma tateB_mul (hpq : (p : F) + q = 1) (σ τ : AbsGal F) :
    tateB p q (σ * τ) =
      if kummerCharFun q τ = 0 then tateB p q σ else sqrtSep p * (tateB p q σ)⁻¹ := by
  have hγ := tateGamma_ne_zero hpq
  have hp := sqrtSep_ne_zero p
  unfold tateB
  rw [kummerCharFun_mul]
  rcases zmod2_cases (kummerCharFun q σ) with h1 | h1 <;>
    rcases zmod2_cases (kummerCharFun q τ) with h2 | h2 <;>
    simp only [h1, h2, add_zero, zero_add, show (1 : ZMod 2) + 1 = 0 from rfl, if_true,
      show (1 : ZMod 2) ≠ 0 from by decide, if_false]
  field_simp

lemma tatePsi_mul (hpq : (p : F) + q = 1) (σ τ : AbsGal F) :
    tatePsi p q (σ * τ) = tatePsi p q σ + tatePsi p q τ + kummerCharFun p σ * kummerCharFun q τ := by
  apply sgn_injective (F := F)
  have hB := tateB_ne_zero hpq σ
  have hp := sqrtSep_ne_zero p
  have e := apply_tateGamma hpq (σ * τ)
  rw [AlgEquiv.mul_apply, apply_tateGamma hpq τ, map_mul, map_sgn, tateB_mul hpq] at e
  rw [sgn_add, sgn_add]
  have hs1 := sgn_mul_self (F := F) (tatePsi p q σ)
  rcases zmod2_cases (kummerCharFun q τ) with h | h
  · have hBτ : tateB p q τ = tateGamma q := by simp [tateB, h]
    rw [hBτ, apply_tateGamma hpq σ, if_pos h] at e
    rw [h, mul_zero, sgn_zero, mul_one]
    have := mul_right_cancel₀ hB (by rw [← e]; ring :
      (sgn (tatePsi p q σ) * sgn (tatePsi p q τ)) * tateB p q σ =
        sgn (tatePsi p q (σ * τ)) * tateB p q σ)
    exact this.symm
  · have hBτ : tateB p q τ = sqrtSep p * (tateGamma q)⁻¹ := by simp [tateB, h]
    rw [hBτ, map_mul, map_inv₀, apply_tateGamma hpq σ, apply_sqrtSep_eq_sgn,
      if_neg (by rw [h]; decide)] at e
    rw [h, mul_one]
    have hkey : sgn (F := F) (tatePsi p q (σ * τ)) * sgn (F := F) (tatePsi p q σ) =
        sgn (F := F) (tatePsi p q τ) * sgn (F := F) (kummerCharFun p σ) := by
      have hs := sgn_ne_zero (F := F) (tatePsi p q σ)
      field_simp at e
      linear_combination -e
    linear_combination (-(sgn (F := F) (tatePsi p q (σ * τ)))) * hs1 +
      sgn (F := F) (tatePsi p q σ) * hkey

lemma continuous_tatePsi : Continuous (tatePsi p q) := by
  let S : Subgroup (AbsGal F) := MulAction.stabilizer (AbsGal F) (sqrtSep q) ⊓
    MulAction.stabilizer (AbsGal F) (tateGamma q)
  let E := IntermediateField.adjoin F ({sqrtSep q, tateGamma q} : Set K)
  have : FiniteDimensional F E :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have hle : E.fixingSubgroup ≤ S := fun σ hσ ↦ by
    have hfix := (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ
    exact ⟨hfix _ (IntermediateField.subset_adjoin F _ (by simp)),
      hfix _ (IntermediateField.subset_adjoin F _ (by simp))⟩
  have hopen : IsOpen (S : Set (AbsGal F)) := Subgroup.isOpen_mono hle E.fixingSubgroup_isOpen
  apply IsLocallyConstant.continuous
  rw [IsLocallyConstant.iff_exists_open]
  intro σ₀
  refine ⟨(fun σ ↦ σ₀⁻¹ * σ) ⁻¹' S, hopen.preimage (continuous_const.mul continuous_id),
    by simp [S, Subgroup.one_mem], fun σ hσ ↦ ?_⟩
  have key : ∀ x ∈ ({sqrtSep q, tateGamma q} : Set K), σ x = σ₀ x := by
    intro x hx
    have hx' : (σ₀⁻¹ * σ) x = x := by
      rcases hx with rfl | rfl
      · exact hσ.1
      · exact hσ.2
    calc σ x = σ₀ ((σ₀⁻¹ * σ) x) := by rw [← AlgEquiv.mul_apply, mul_inv_cancel_left]
      _ = σ₀ x := by rw [hx']
  unfold tatePsi
  rw [key _ (by simp), key _ (by simp)]

end Tate

section Assembly

universe u

lemma classOf_congr' {k G M : Type u} [Ring k] [TopologicalSpace k] [IsTopologicalRing k] [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [AddCommGroup M]
    [Module k M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousSMul k M] {n : ℕ}
    {F₁ F₂ : C(Fin (n + 1) → G, M)} (e : F₁ = F₂) (h₁ h₂ h₁' h₂') :
    classOf k n F₁ h₁ h₂ = classOf k n F₂ h₁' h₂' := by
  subst e; rfl

variable {F : Type} [Field F] [NeZero (2 : F)]

lemma kummerCharFun_sub (c : Fˣ) (u v : AbsGal F) :
    kummerCharFun c v - kummerCharFun c u = kummerCharFun c (u⁻¹ * v) := by
  have := kummerCharFun_mul c u (u⁻¹ * v)
  rw [mul_inv_cancel_left] at this
  rw [this]; ring

end Assembly

end MilnorConjecture

open MilnorConjecture in
theorem solution (F : Type) [Field F] [NeZero (2 : F)] (n : ℕ)
    (a : Fin n → Fˣ) (i j : Fin n) (hij : (i : ℕ) + 1 = j) (h : (a i : F) + (a j : F) = 1) :
    galoisSymbol a = 0 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  set p := a i
  set q := a j
  let χ : Fin (m + 2) → AbsGal F → ZMod 2 := fun l ↦ kummerCharFun (a l)
  let Ψ : AbsGal F → AbsGal F → ZMod 2 := fun u v ↦ tatePsi p q (u⁻¹ * v)
  have hi : (⟨i, by omega⟩ : Fin (m + 2)) = i := rfl
  have hj : (⟨(i : ℕ) + 1, by omega⟩ : Fin (m + 2)) = j := Fin.ext hij
  have hΨ : ∀ u v w, Ψ v w - Ψ u w + Ψ u v =
      (χ ⟨i, by omega⟩ v - χ ⟨i, by omega⟩ u) *
        (χ ⟨(i : ℕ) + 1, by omega⟩ w - χ ⟨(i : ℕ) + 1, by omega⟩ v) := by
    intro u v w
    simp only [χ, Ψ, hi, hj, kummerCharFun_sub]
    have hmul := tatePsi_mul h (u⁻¹ * v) (v⁻¹ * w)
    rw [show u⁻¹ * v * (v⁻¹ * w) = u⁻¹ * w by group] at hmul
    rw [hmul, show ∀ A B C : ZMod 2, B - (A + B + C) + A = -C from fun A B C ↦ by ring,
      ZMod.neg_eq_self_mod_two]
  obtain ⟨Θ, hΘc, hΘinv, hΘ⟩ := exists_prodCochain_eq_fcob (i : ℕ) m χ (by omega) Ψ hΨ
    (fun l ↦ continuous_kummerCharFun (a l))
    (fun l g x z ↦ by simp only [χ, kummerCharFun_mul]; ring)
    (continuous_tatePsi.comp (continuous_fst.inv.mul continuous_snd))
    (fun g u v ↦ by simp only [Ψ]; congr 1; group)
  let Θc : C(Fin (m + 2) → AbsGal F, ZMod 2) := ⟨Θ, hΘc⟩
  have hcob : coboundary (m + 2) Θc = symbolCochain a := by
    ext y
    rw [coboundary_apply]
    change _ = prodCochain χ y
    rw [hΘ y]
    simp [fcob, Θc, zsmul_eq_mul]
  have hinv : ∀ (g : AbsGal F) (v : Fin (m + 3) → AbsGal F),
      coboundary (m + 2) Θc (fun i ↦ g * v i) = coboundary (m + 2) Θc v := by
    rw [hcob]; exact symbolCochain_invariant a
  have hcoc : coboundary (m + 3) (coboundary (m + 2) Θc) = 0 := by
    rw [hcob]; exact coboundary_symbolCochain a
  change classOf (ZMod 2) (m + 2) (symbolCochain a) _ _ = 0
  rw [classOf_congr' hcob.symm _ _ hinv hcoc]
  exact classOf_coboundary_eq_zero Θc hΘinv hinv hcoc
