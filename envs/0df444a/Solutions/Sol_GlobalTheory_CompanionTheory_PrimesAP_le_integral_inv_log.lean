-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesAP.le_integral_inv_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:21.084892+00:00
-- url     : https://prove2.me/submissions/17373800-3040-4943-9c8b-d7faa7afc3d2

import Mathlib
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_AutomorphicForms__IsExcRat_5b5b692fee064c30
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LFunctionConjEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZeroFreePrincipal
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesAP_intervalIntegrable_inv_log

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset DirichletCharacter
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesAP
namespace GlobalTheory.CompanionTheory.PrimesAP
theorem _root_.solution {Y X : ℝ} (hY : 2 ≤ Y) (hX : Y ≤ X) :
    (X - Y) / Real.log X ≤ ∫ t in Y..X, 1 / Real.log t := by
  have : (X - Y) / Real.log X = ∫ _ in Y..X, 1 / Real.log X := by
    simp [div_eq_mul_inv]
  rw [this]
  apply intervalIntegral.integral_mono_on hX (by simp) (intervalIntegrable_inv_log hY (hY.trans hX))
  intro t ht
  exact one_div_le_one_div_of_le (Real.log_pos (by linarith [ht.1])) (Real.log_le_log (by linarith [ht.1]) ht.2)
end GlobalTheory.CompanionTheory.PrimesAP
