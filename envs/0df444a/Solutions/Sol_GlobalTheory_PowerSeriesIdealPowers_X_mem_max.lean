-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.X_mem_max
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:32.089548+00:00
-- url     : https://prove2.me/submissions/0e2996e6-b5f0-4288-be28-8bb530ea5a7b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MemPowOfCoeffMem
import Theorems.Thm_GlobalTheory_PowerSeriesIdealPowers_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PowerSeriesIdealPowers
open MvPowerSeries IsLocalRing
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.PowerSeriesIdealPowers
theorem _root_.solution {σ : Type} (i : σ) : (X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := by
  rw [mem_max_iff, constantCoeff_X]; exact zero_mem _
end GlobalTheory.PowerSeriesIdealPowers
