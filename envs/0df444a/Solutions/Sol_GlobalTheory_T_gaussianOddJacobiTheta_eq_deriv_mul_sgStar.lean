-- Prove2me | solution 1 for GlobalTheory.T.gaussianOddJacobiTheta_eq_deriv_mul_sgStar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:48:16.568629+00:00
-- url     : https://prove2.me/submissions/a4b60b14-b7db-4137-910a-aa8899f8d08c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStarStatement
import Theorems.Thm_GlobalTheory_SgStarOddTheta_exp_mul_oddTheta_eq_deriv_mul_sgStar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : Formalism.L2.Th1.F.ThetaLine → Formalism.L2.Th1.F.SgStarBasic → ∀ (τ : UpperHalfPlane) (z : ℂ), Complex.exp ((Real.pi : ℂ) * z ^ 2 / (2 * ((τ.im : ℝ) : ℂ))) * GlobalTheory.ThetaWeberRoad.oddTheta τ z = deriv (GlobalTheory.ThetaWeberRoad.oddTheta τ) 0 * Formalism.L2.Th1.F.sgStar (GlobalTheory.periodPairOfTau τ) z := by
  first | exact @GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | exact GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar | (intros; apply GlobalTheory.SgStarOddTheta.exp_mul_oddTheta_eq_deriv_mul_sgStar <;> assumption)
end _root_.GlobalTheory.T
