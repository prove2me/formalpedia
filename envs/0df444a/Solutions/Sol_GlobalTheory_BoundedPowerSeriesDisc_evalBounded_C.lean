-- Prove2me | solution 1 for GlobalTheory.BoundedPowerSeriesDisc.evalBounded_C
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:44:43.964768+00:00
-- url     : https://prove2.me/submissions/f3212c88-5f27-4599-afbb-30b43866c8e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SummableNormBoundedSeries
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
theorem _root_.solution (c : F) :
    evalBounded π hπ ⟨C c, C_mem_boundedSeries c⟩ = c := by
  rw [evalBounded_apply]
  exact tsum_coeff_C c π
end GlobalTheory.BoundedPowerSeriesDisc
