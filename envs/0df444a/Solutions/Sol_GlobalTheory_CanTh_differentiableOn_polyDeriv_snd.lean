-- Prove2me | solution 1 for GlobalTheory.CanTh.differentiableOn_polyDeriv_snd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:43:30.009697+00:00
-- url     : https://prove2.me/submissions/7deaae27-28a8-4b09-866f-34a9e02f469c

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_GCauchyStatement
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DifferentiableOnOfTendstoLocallyUniformlyOn
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_SetIntegralPowEqZeroOfPosFreqEuclidean
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_MemThetaDomainIffIsSiegelAddTranspose
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsMulDotProductLeOfIsCompactThetaDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_DifferentiableOnThetaProdOfNormal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_HasSumPolyDerivMulProdAddMatrix
import Theorems.Thm_GlobalTheory_CanTh_iteratedFDeriv_snd
import Theorems.Thm_GlobalTheory_SCV_differentiableOn_iteratedFDeriv


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
variable {B : Type*} [NormedAddCommGroup B] [NormedSpace ℂ B] [FiniteDimensional ℂ B]
namespace GlobalTheory.CanTh
theorem _root_.solution {F : B × W → ℂ} {U : Set (B × W)} (hU : IsOpen U)
    (hF : DifferentiableOn ℂ F U) (P : MvPolynomial σ ℂ) (u : σ → W) :
    DifferentiableOn ℂ (fun p : B × W => I2.polyDeriv P u (fun w => F (p.1, w)) p.2) U := by
  unfold I2.polyDeriv
  refine DifferentiableOn.fun_sum fun m _ => DifferentiableOn.const_mul ?_ _
  refine DifferentiableOn.congr ?_ fun p hp => iteratedFDeriv_snd hU hF (s := p.1) (x := p.2) hp _ _
  exact (ContinuousMultilinearMap.apply ℂ (fun _ => B × W) ℂ _).differentiable.comp_differentiableOn
    (SCV.differentiableOn_iteratedFDeriv hU hF _)
end GlobalTheory.CanTh
