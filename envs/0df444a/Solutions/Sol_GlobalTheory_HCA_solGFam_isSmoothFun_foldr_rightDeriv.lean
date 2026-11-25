-- Prove2me | solution 1 for GlobalTheory.HCA.solGFam_isSmoothFun_foldr_rightDeriv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T07:36:49.765488+00:00
-- url     : https://prove2.me/submissions/af4a3cf5-83c6-4776-948e-e3900a6e6257

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsExpLieAlgebraComplexUnits
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DerivWordLeIntegralOfAevalCasimirEqZeroStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeftTranslateSmoothCommuteLeftInvariantOpsStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LaplacePolynomialKernelDerivativeWordsFamily

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.HCA
variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]
  {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (h : IsExpLieAlgebra G 𝔤)
namespace GlobalTheory.HCA
theorem _root_.solution (l : List 𝔤) {f : G → ℂ} (hf : h.IsSmoothFun f) :
    h.IsSmoothFun (l.foldr h.rightDeriv f) := by
  induction l with
  | nil => exact hf
  | cons X l ih => exact h.isSmoothFun_rightDeriv ih X
end GlobalTheory.HCA
