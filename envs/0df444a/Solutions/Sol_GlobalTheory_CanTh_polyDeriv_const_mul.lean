-- Prove2me | solution 1 for GlobalTheory.CanTh.polyDeriv_const_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:05:32.326616+00:00
-- url     : https://prove2.me/submissions/1af9e506-69d7-48d8-9561-1245d1bad741

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
import Theorems.Thm_GlobalTheory_SCV_contDiffAt_of_differentiableOn
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open Complex Matrix Filter Topology ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Real
open GlobalTheory GlobalTheory.CanTh
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
namespace GlobalTheory.CanTh
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) {F : W → ℂ} {U : Set W}
    (hU : IsOpen U) (hF : DifferentiableOn ℂ F U) (c : ℂ) {x : W} (hx : x ∈ U) :
    I2.polyDeriv P u (fun w => c * F w) x = c * I2.polyDeriv P u F x := by
  unfold I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : (fun w => c * F w) = c • F := rfl
  rw [e, iteratedFDeriv_const_smul_apply
    (SCV.contDiffAt_of_differentiableOn hF (hU.mem_nhds hx) _)]
  simp only [ContinuousMultilinearMap.smul_apply, smul_eq_mul]
  ring
end GlobalTheory.CanTh
