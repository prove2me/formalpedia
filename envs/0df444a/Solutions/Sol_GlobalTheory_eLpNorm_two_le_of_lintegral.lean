-- Prove2me | solution 1 for GlobalTheory.eLpNorm_two_le_of_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T03:35:32.601735+00:00
-- url     : https://prove2.me/submissions/6d3123b3-89af-4089-b7dd-52be413571bb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_ExtendAeLinearOfLocalSqBoundDense

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Q E : Type} [MeasurableSpace Q] [NormedAddCommGroup E]
    (ν : Measure Q) (g : Q → E) (B : ℝ) (hB : 0 ≤ B)
    (h : ∫⁻ x, ‖g x‖ₑ ^ 2 ∂ν ≤ ENNReal.ofReal (B ^ 2)) :
    eLpNorm g 2 ν ≤ ENNReal.ofReal B := by
  have e := eLpNorm_nnreal_pow_eq_lintegral (f := g) (μ := ν) (p := 2) (by norm_num)
  simp only [NNReal.coe_ofNat, ENNReal.coe_ofNat, ENNReal.rpow_ofNat] at e
  rw [← e, ENNReal.ofReal_pow hB] at h
  exact (ENNReal.pow_le_pow_left_iff two_ne_zero).1 h
end GlobalTheory
