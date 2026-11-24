-- Prove2me | solution 1 for GlobalTheory.MaximalIdealFiltration.maximalIdeal_pow_le_filt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:13:27.363887+00:00
-- url     : https://prove2.me/submissions/89502e4e-d582-4300-bef5-352f8a87452a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MaximalIdealLeFiltOne
import Theorems.Thm_GlobalTheory_MaximalIdealFiltration_mul_mem_filt
import Theorems.Thm_GlobalTheory_MaximalIdealFiltration_maximalIdeal_le_filt_one

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.MaximalIdealFiltration
open MvPowerSeries
variable {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
namespace GlobalTheory.MaximalIdealFiltration
theorem _root_.solution (N : ℕ) :
    IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ^ N ≤ filt (O := O) N := by
  induction N with
  | zero =>
    intro f _ m
    simp
  | succ n ih =>
    rw [pow_succ, Ideal.mul_le]
    intro r hr s hs
    exact mul_mem_filt (ih hr) (maximalIdeal_le_filt_one hs)
end GlobalTheory.MaximalIdealFiltration
