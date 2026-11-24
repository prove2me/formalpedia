-- Prove2me | solution 1 for GlobalTheory.FiltrationMultiplicative.pow_le_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:27:04.078467+00:00
-- url     : https://prove2.me/submissions/d1ca0584-c992-42fd-bb0e-cadca2bcc7d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_FiltLePow
import Theorems.Thm_GlobalTheory_FiltrationMultiplicative_max_le_filt_one

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
theorem _root_.solution {σ : Type} (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries σ O) ^ N ≤ FiltIdeal O σ N := by
  induction N with
  | zero => intro f _; exact filt_zero f
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact filt_mul (ih hr) (max_le_filt_one hs)
end GlobalTheory.FiltrationMultiplicative
