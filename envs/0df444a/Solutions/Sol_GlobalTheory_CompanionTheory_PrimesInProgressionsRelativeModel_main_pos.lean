-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.main_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:37:38.035218+00:00
-- url     : https://prove2.me/submissions/5d300401-4d05-47e8-ba94-145172d95ace

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_invLog_intervalIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_invLog_integral_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators Classical
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
namespace GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
theorem _root_.solution {X Y θ : ℝ} (hθ : θ ≤ 1) (hY : 2 ≤ Y) (hYX : Y < X) :
    0 < (∫ t in (2 : ℝ)..X, 1 / Real.log t) - θ * ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (invLog_intervalIntegrable (le_refl 2) hY) (invLog_intervalIntegrable hY (by linarith : (2:ℝ) ≤ X))
  have h2 := invLog_integral_pos hY hYX
  have h3 : 0 ≤ ∫ t in (2 : ℝ)..Y, 1 / Real.log t := by
    rcases hY.eq_or_lt with h | h
    · subst h; simp
    · exact (invLog_integral_pos le_rfl h).le
  nlinarith
end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
