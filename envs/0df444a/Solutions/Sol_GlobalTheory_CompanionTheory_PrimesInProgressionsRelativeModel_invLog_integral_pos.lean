-- Prove2me | solution 1 for GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel.invLog_integral_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T12:55:22.280801+00:00
-- url     : https://prove2.me/submissions/8d01bb1b-a4d9-4af8-aff0-32c5567d837b

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_PrimesInProgressionsRelative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_PrimesInProgressionsRelativeOfTzRat
import Definitions.Def_Development_AutomorphicSpectrum_PublishedTheorems_PublishedGlobalResults_InvLogIntervalIntegrable
import Theorems.Thm_GlobalTheory_CompanionTheory_PrimesInProgressionsRelativeModel_invLog_intervalIntegrable

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
theorem _root_.solution {u v : ℝ} (hu : 2 ≤ u) (huv : u < v) :
    0 < ∫ t in u..v, 1 / Real.log t := by
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (invLog_intervalIntegrable hu (by linarith)) ?_ huv
  intro t ht
  exact one_div_pos.2 (Real.log_pos (by linarith [ht.1]))
end GlobalTheory.CompanionTheory.PrimesInProgressionsRelativeModel
