-- Prove2me | solution 1 for GlobalTheory.norm_prod_sign_mul_det_submatrix_sub_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:43:14.125718+00:00
-- url     : https://prove2.me/submissions/c0da3d1c-b30c-47c7-a707-65add9f21d40

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CuspidalExponentialDecay
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_TaylorDiscriminants_DiscriminantEstimates_DiscriminantTheorems_ScaledBoundInequality
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ImportsAlt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_NormProdSignMulDetSubmatrixSubOneLe
import Theorems.Thm_GlobalTheory_norm_det_one_add_sub_one_le_exp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField ReciprocityTheory.ChartRestriction.G.FD
open Matrix hiding gram
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {r : ℕ} (j : Fin r → ℂ)
    (hj : ∀ a, j a = 1 ∨ j a = -1) (G : Matrix (Fin r) (Fin r) ℂ) {ε : ℝ} (hε : 0 ≤ ε)
    (hG : ∀ a b, ‖(G - diagonal j) a b‖ ≤ ε) (hr : (r : ℝ) ^ 2 * ε ≤ 1)
    {i : ℕ} {e : Fin i → Fin r} (he : Function.Injective e) :
    ‖(∏ a, j (e a)) * (G.submatrix e e).det - 1‖ ≤ 2 * ((r : ℝ) ^ 2 * ε) := by
  have hi : (i : ℝ) ≤ r := by
    have := Fintype.card_le_of_injective e he
    simp only [Fintype.card_fin] at this
    exact_mod_cast this
  have h1 : diagonal (fun a => j (e a)) * G.submatrix e e =
      1 + diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e := by
    ext a b
    by_cases h : a = b
    · subst h
      rcases hj (e a) with h | h <;> simp [h]
    · simp [h, he.eq_iff, diagonal_apply]
  have h2 := norm_det_one_add_sub_one_le_exp
    (diagonal (fun a => j (e a)) * (G - diagonal j).submatrix e e) hε (fun a b => by
      rw [diagonal_mul, norm_mul, submatrix_apply]
      rcases hj (e a) with h | h <;> simpa [h] using hG _ _)
  rw [← h1, det_mul, det_diagonal, Fintype.card_fin] at h2
  have h3 : (i : ℝ) * (i * ε) ≤ (r : ℝ) ^ 2 * ε := by
    rw [sq, mul_assoc]; gcongr
  have h4 := Real.exp_le_exp.2 h3
  have h0 : 0 ≤ (r : ℝ) ^ 2 * ε := by positivity
  have h5 := Real.abs_exp_sub_one_le (x := (r : ℝ) ^ 2 * ε) (by rwa [abs_of_nonneg h0])
  rw [abs_of_nonneg h0] at h5
  linarith [le_abs_self (Real.exp ((r : ℝ) ^ 2 * ε) - 1)]
end GlobalTheory
