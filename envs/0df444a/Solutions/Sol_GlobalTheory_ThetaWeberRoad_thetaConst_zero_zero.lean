-- Prove2me | solution 1 for GlobalTheory.ThetaWeberRoad.thetaConst_zero_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:34:02.258876+00:00
-- url     : https://prove2.me/submissions/2f48236a-a749-4672-b940-2a71ca805c86

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
theorem _root_.solution (τ : UpperHalfPlane) :
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst 0 0 τ = jacobiTheta₂ 0 τ := by
  simp [GlobalTheory.IndefiniteRowSideFullHecke.ThetaConstantWeber.thetaConst]
end GlobalTheory.ThetaWeberRoad
