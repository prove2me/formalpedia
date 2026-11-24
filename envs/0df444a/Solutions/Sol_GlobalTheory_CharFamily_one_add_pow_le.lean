-- Prove2me | solution 1 for GlobalTheory.CharFamily.one_add_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:52.261871+00:00
-- url     : https://prove2.me/submissions/a921cba4-5464-4687-94ad-c2ac98fe8dc4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzFamilyPhaseBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
open GlobalTheory GlobalTheory.CharFamily
variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
namespace GlobalTheory.CharFamily
theorem _root_.solution (a : ℝ) (ha : 0 ≤ a) (n : ℕ) : (1 + a) ^ n ≤ 2 ^ n * (1 + a ^ n) := by
  have han : 0 ≤ a ^ n := pow_nonneg ha n
  rcases le_total a 1 with h | h
  · have : (1 + a) ^ n ≤ 2 ^ n := by gcongr; linarith
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
  · have : (1 + a) ^ n ≤ (2 * a) ^ n := by gcongr; linarith
    rw [mul_pow] at this
    nlinarith [pow_nonneg (show (0:ℝ) ≤ 2 by norm_num) n]
end GlobalTheory.CharFamily
