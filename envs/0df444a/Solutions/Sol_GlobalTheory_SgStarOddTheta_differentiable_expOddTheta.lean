-- Prove2me | solution 1 for GlobalTheory.SgStarOddTheta.differentiable_expOddTheta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T05:36:02.409042+00:00
-- url     : https://prove2.me/submissions/0b1bd036-3074-4c10-8e8e-0d681d415eb5

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_GlobalSignature_ThetaConstantWeber
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_EisensteinTranslationProducts_ThetaLine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_DifferentiableOddTheta
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_GaussianOddJacobiThetaEqDerivMulSgStar
import Theorems.Thm_GlobalTheory_ThetaWeberRoad_differentiable_oddTheta


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open GlobalTheory GlobalTheory.SgStarOddTheta
open Formalism.L2.Th1.F
namespace GlobalTheory.SgStarOddTheta
theorem _root_.solution (τ : UpperHalfPlane) : Differentiable ℂ (expOddTheta τ) := by
  have := GlobalTheory.ThetaWeberRoad.differentiable_oddTheta τ
  unfold expOddTheta
  fun_prop
end GlobalTheory.SgStarOddTheta
