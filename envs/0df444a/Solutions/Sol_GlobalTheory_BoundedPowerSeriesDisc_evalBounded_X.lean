-- Prove2me | solution 1 for GlobalTheory.BoundedPowerSeriesDisc.evalBounded_X
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:17:00.830356+00:00
-- url     : https://prove2.me/submissions/9565ab21-489a-452b-a3ed-44283ca8c198

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_tsum_coeff_X
import Theorems.Thm_GlobalTheory_BoundedPowerSeriesDisc_evalBounded_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.BoundedPowerSeriesDisc
open PowerSeries
variable {F : Type*} [NormedField F] [IsUltrametricDist F]
variable [CompleteSpace F]
variable (π : F) (hπ : ‖π‖ < 1)
namespace GlobalTheory.BoundedPowerSeriesDisc
theorem _root_.solution : evalBounded π hπ ⟨X, X_mem_boundedSeries⟩ = π := by
  rw [evalBounded_apply]
  exact tsum_coeff_X π
end GlobalTheory.BoundedPowerSeriesDisc
