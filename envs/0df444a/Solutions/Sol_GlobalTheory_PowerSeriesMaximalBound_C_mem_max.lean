-- Prove2me | solution 1 for GlobalTheory.PowerSeriesMaximalBound.C_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:29:28.688922+00:00
-- url     : https://prove2.me/submissions/85a5acdf-78c3-447c-b179-a7d3b3f2e0b4

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
theorem _root_.solution {r : O} (hr : r ∈ IsLocalRing.maximalIdeal O) :
    (C r : MvPowerSeries (Fin a) O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, isUnit_iff_constantCoeff, constantCoeff_C]
  exact hr
end GlobalTheory.PowerSeriesMaximalBound
