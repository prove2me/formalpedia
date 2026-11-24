-- Prove2me | solution 1 for GlobalTheory.Phase.ParabValues.ph_rat_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:26:05.016298+00:00
-- url     : https://prove2.me/submissions/62dcf4b3-2e85-49ee-90cc-22e2d6e0b4b1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_EqOfSiegelThetaSeriesRationalEq
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelThetaTransformationSiegelParabolic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SiegelParabolicTransformPhase

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW GlobalTheory.Phase
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.Phase GlobalTheory.Phase.ParabValues
open GlobalTheory.SW.Parab
namespace GlobalTheory.Phase.ParabValues
theorem _root_.solution (r q : ℚ) : Ph ((r : ℂ) * cexp (-(Real.pi * I * (q : ℂ)))) := by
  refine ⟨2 * q.den, by have := q.den_pos; omega, ?_⟩
  have hn : ‖cexp (-(Real.pi * I * (q : ℂ)))‖ = 1 := by
    have : -(Real.pi * I * (q : ℂ)) = ((-(Real.pi * q) : ℝ) : ℂ) * I := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have he : cexp (-(Real.pi * I * (q : ℂ))) ^ (2 * q.den) = 1 := by
    rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
    refine ⟨-q.num, ?_⟩
    have h : (q : ℂ) * (q.den : ℂ) = (q.num : ℂ) := by exact_mod_cast Rat.mul_den_eq_num q
    push_cast
    rw [← h]
    ring
  rw [mul_pow, he, mul_one, norm_mul, hn, mul_one, Complex.norm_ratCast]
  have : (|(r : ℝ)|) ^ (2 * q.den) = (r : ℝ) ^ (2 * q.den) := Even.pow_abs ⟨q.den, by ring⟩ _
  rw [← Complex.ofReal_pow, this]
  push_cast
  rfl
end GlobalTheory.Phase.ParabValues
