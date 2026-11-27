-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.exp_neg_half_pi_I
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:33:12.455562+00:00
-- url     : https://prove2.me/submissions/491e8f49-5515-4689-8ce3-5f13a64711db

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
noncomputable section
open GlobalTheory GlobalTheory.ThetaWeberRoad
namespace GlobalTheory.ThetaWeberRoad
theorem _root_.solution : cexp (-((π : ℂ) * I / 2)) = -I := by
  rw [show -((π : ℂ) * I / 2) = -π / 2 * I by ring]
  exact Complex.exp_neg_pi_div_two_mul_I
end GlobalTheory.ThetaWeberRoad
