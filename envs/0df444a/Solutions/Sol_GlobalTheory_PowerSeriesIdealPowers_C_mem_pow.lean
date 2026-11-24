-- Prove2me | solution 1 for GlobalTheory.PowerSeriesIdealPowers.C_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:29:31.245034+00:00
-- url     : https://prove2.me/submissions/1f9b110a-518f-4090-90a0-848da8480172

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
theorem _root_.solution {σ : Type} (n : ℕ) (c : O) (hc : c ∈ (maximalIdeal O) ^ n) :
    C c ∈ (maximalIdeal (MvPowerSeries σ O)) ^ n := by
  have h1 : C c ∈ Ideal.map (C (σ := σ)) ((maximalIdeal O) ^ n) := Ideal.mem_map_of_mem _ hc
  rw [Ideal.map_pow] at h1
  refine Ideal.pow_right_mono ?_ n h1
  rw [Ideal.map_le_iff_le_comap]
  intro x hx
  rw [Ideal.mem_comap, mem_max_iff, constantCoeff_C]
  exact hx
end GlobalTheory.PowerSeriesIdealPowers
