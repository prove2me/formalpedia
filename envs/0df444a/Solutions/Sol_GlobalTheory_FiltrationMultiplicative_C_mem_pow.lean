-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.C_mem_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T15:02:29.092573+00:00
-- url     : https://prove2.me/submissions/2ebdbcd4-849a-4a6c-8fb5-f5b76584517b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_mem_max_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPowerSeries
open GlobalTheory GlobalTheory.FiltrationMultiplicative
variable {O : Type} [CommRing O] [IsLocalRing O]
namespace GlobalTheory.FiltrationMultiplicative
theorem _root_.solution {σ : Type} (n : ℕ) {c : O} (hc : c ∈ IsLocalRing.maximalIdeal O ^ n) :
    (C c : MvPowerSeries σ O) ∈ IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ n := by
  have h1 : Ideal.map (C : O →+* MvPowerSeries σ O) (IsLocalRing.maximalIdeal O) ≤
      IsLocalRing.maximalIdeal (MvPowerSeries σ O) := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap, mem_max_iff, coeff_zero_C]
    exact hx
  have h2 := Ideal.mem_map_of_mem (C : O →+* MvPowerSeries σ O) hc
  rw [Ideal.map_pow] at h2
  exact Ideal.pow_right_mono h1 n h2
end GlobalTheory.FiltrationMultiplicative
