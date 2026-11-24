-- Prove2me | solution 1 for GlobalTheory.PowerSeriesMaximalBound.X_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:29.446849+00:00
-- url     : https://prove2.me/submissions/d400a00d-f73b-45ac-8a22-d6120a2f9c1f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesMaximalBound
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
namespace GlobalTheory.PowerSeriesMaximalBound
theorem _root_.solution (i : Fin a) :
    (X i : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_X]
  exact not_isUnit_zero
end GlobalTheory.PowerSeriesMaximalBound
