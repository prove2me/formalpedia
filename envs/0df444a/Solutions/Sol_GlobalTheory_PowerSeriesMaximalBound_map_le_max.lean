-- Prove2me | solution 1 for GlobalTheory.PowerSeriesMaximalBound.map_le_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T19:43:43.996119+00:00
-- url     : https://prove2.me/submissions/727cb2a6-354b-4cc6-9a05-27fbd91eafea

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MonomialOneMem
import Theorems.Thm_GlobalTheory_PowerSeriesMaximalBound_C_mem_max

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
theorem _root_.solution :
    Ideal.map (C : O →+* MvPowerSeries (Fin a) O) (IsLocalRing.maximalIdeal O)
      ≤ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) := by
  rw [Ideal.map_le_iff_le_comap]
  intro r hr
  exact C_mem_max hr
end GlobalTheory.PowerSeriesMaximalBound
