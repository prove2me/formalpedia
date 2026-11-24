-- Prove2me | solution 1 for GlobalTheory.MultilinearMap.inner_map_eq_const_mul_prod_inner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T22:57:40.874044+00:00
-- url     : https://prove2.me/submissions/8491718d-7844-4b6b-83e5-382e6dd6c83c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_InnerMapEqConstMulProdInner

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
open GlobalTheory
namespace GlobalTheory
namespace MultilinearMap
theorem _root_.solution
    {ι : Type} [Fintype ι] {Xs : ι → Type} [∀ i, NormedAddCommGroup (Xs i)]
    [∀ i, InnerProductSpace ℂ (Xs i)] {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (f : MultilinearMap ℂ Xs E) (K : ℝ) (hf : ∀ x, ‖f x‖ ^ 2 = K * ∏ i, ‖x i‖ ^ 2) :
    ∀ x y, ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
  classical
  have hdiag : ∀ x, ⟪f x, f x⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, x i⟫_ℂ := by
    intro x
    simp only [inner_self_eq_norm_sq_to_K]
    have h := congrArg (fun r : ℝ => (r : ℂ)) (hf x)
    simp only [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_prod] at h
    exact h
  have hprod : ∀ (x y : ∀ i, Xs i) (j : ι) (u v : Xs j),
      ∏ i, ⟪Function.update x j u i, Function.update y j v i⟫_ℂ
        = ⟪u, v⟫_ℂ * ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ := by
    intro x y j u v
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j)]
    simp only [Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun i hi => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi),
      Function.update_of_ne (Finset.ne_of_mem_erase hi)]
  have key : ∀ s : Finset ι, ∀ x y : (∀ i, Xs i), (∀ i ∉ s, x i = y i) →
      ⟪f x, f y⟫_ℂ = (K : ℂ) * ∏ i, ⟪x i, y i⟫_ℂ := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro x y h
      have hxy : x = y := funext fun i => h i (Finset.notMem_empty i)
      subst hxy
      exact hdiag x
    | insert j s hj ih =>
      intro x y hxy
      set C := ∏ i ∈ Finset.univ.erase j, ⟪x i, y i⟫_ℂ with hC
      have hd : ∀ u : Xs j, ⟪f (Function.update x j u), f (Function.update y j u)⟫_ℂ
          = (K : ℂ) * (⟪u, u⟫_ℂ * C) := by
        intro u
        rw [ih _ _ ?_, hprod]
        intro i hi
        by_cases hij : i = j
        · subst hij; simp
        · rw [Function.update_of_ne hij, Function.update_of_ne hij]
          exact hxy i (by simp [hij, hi])
      have hab : ∀ a b : Xs j, ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
          = (K : ℂ) * (⟪a, b⟫_ℂ * C) := by
        intro a b
        have ha := hd a
        have hb := hd b
        have h1 := hd (a + b)
        have h2 := hd (a + Complex.I • b)
        simp only [MultilinearMap.map_update_add, MultilinearMap.map_update_smul, inner_add_left,
          inner_add_right, inner_smul_left, inner_smul_right, Complex.conj_I] at h1 h2
        have e1 : ⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            + ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            = (K : ℂ) * C * (⟪a, b⟫_ℂ + ⟪b, a⟫_ℂ) := by
          linear_combination h1 - ha - hb
        have e2 : Complex.I * (⟪f (Function.update x j a), f (Function.update y j b)⟫_ℂ
            - ⟪f (Function.update x j b), f (Function.update y j a)⟫_ℂ
            - (K : ℂ) * C * (⟪a, b⟫_ℂ - ⟪b, a⟫_ℂ)) = 0 := by
          linear_combination h2 - ha + Complex.I * Complex.I * hb
        have e3 := (mul_eq_zero.mp e2).resolve_left Complex.I_ne_zero
        linear_combination (e1 + e3) / 2
      have := hab (x j) (y j)
      simp only [Function.update_eq_self] at this
      rw [this, ← hprod x y j (x j) (y j)]
      simp only [Function.update_eq_self]
  intro x y
  exact key Finset.univ x y (fun i hi => absurd (Finset.mem_univ i) hi)
end MultilinearMap
end GlobalTheory
