-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesAP.mainTerm_pos_model
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T13:12:19.397978+00:00
-- url     : https://prove2.me/submissions/264d1924-9a70-43c1-a845-705c00d398d8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_intervalIntegrable_inv_log
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_le_integral_inv_log


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesAP
namespace GlobalTheory.CompanionTheory.PrimesAP
theorem _root_.solution {θ β X : ℝ} (hX : 4 ≤ X) (h : θ = 0 ∨ (θ ≤ 1 ∧ 1 / 2 ≤ β ∧ β < 1)) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  rcases h with rfl | ⟨h1, h2, h3⟩
  · rw [zero_mul, sub_zero]
    exact lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log le_rfl (by linarith))
  · have hY : 2 ≤ X ^ β := by
      calc (2 : ℝ) = 4 ^ (1 / 2 : ℝ) := by
            rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
        _ ≤ X ^ (1 / 2 : ℝ) := Real.rpow_le_rpow (by norm_num) hX (by norm_num)
        _ ≤ X ^ β := Real.rpow_le_rpow_of_exponent_le (by linarith) h2
    have hYX : X ^ β < X := by
      have := Real.rpow_lt_rpow_of_exponent_lt (x := X) (by linarith) h3
      rwa [Real.rpow_one] at this
    have h5 : 0 < ∫ t in X ^ β..X, 1 / Real.log t :=
      lt_of_lt_of_le (div_pos (by linarith) hL) (le_integral_inv_log hY hYX.le)
    have h6 := intervalIntegral.integral_add_adjacent_intervals
      (intervalIntegrable_inv_log le_rfl hY) (intervalIntegrable_inv_log hY (X := X) (by linarith))
    have h7 : 0 ≤ ∫ t in (2 : ℝ)..X ^ β, 1 / Real.log t := by
      refine le_trans ?_ (le_integral_inv_log le_rfl hY)
      exact div_nonneg (by linarith) (Real.log_nonneg (by linarith))
    nlinarith
end GlobalTheory.CompanionTheory.PrimesAP
