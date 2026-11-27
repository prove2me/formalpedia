-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.negI_mul_cexp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:37:50.985105+00:00
-- url     : https://prove2.me/submissions/4e1c4ff3-fe0d-4ddf-ba33-73c0daec0992

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_HalfPeriodDiffThetaFourthOfSigmaStarAddition
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_exp_neg_half_pi_I

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
theorem _root_.solution (x : ℂ) : -I * cexp x = cexp (-((π : ℂ) * I / 2) + x) := by
  rw [Complex.exp_add, exp_neg_half_pi_I]
end GlobalTheory.ThetaWeberRoad
