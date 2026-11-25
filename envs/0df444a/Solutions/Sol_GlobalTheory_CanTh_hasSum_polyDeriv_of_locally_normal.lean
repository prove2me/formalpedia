-- Prove2me | solution 1 for GlobalTheory.CanTh.hasSum_polyDeriv_of_locally_normal
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:03:26.897133+00:00
-- url     : https://prove2.me/submissions/ec9b4569-a959-4591-ad6c-50170fbda06a

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
import Theorems.Thm_GlobalTheory_SCV_hasSum_iteratedFDeriv_of_locally_normal


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
namespace GlobalTheory.CanTh
theorem _root_.solution {ι : Type*} {F : ι → W → ℂ} {U : Set W} (hU : IsOpen U)
    (hF : ∀ i, DifferentiableOn ℂ (F i) U)
    (hle : ∀ x ∈ U, ∃ t ∈ 𝓝 x, ∃ v : ι → ℝ, Summable v ∧ ∀ i, ∀ z ∈ t, ‖F i z‖ ≤ v i)
    (P : MvPolynomial σ ℂ) (u : σ → W) {x : W} (hx : x ∈ U) :
    HasSum (fun i => I2.polyDeriv P u (F i) x) (I2.polyDeriv P u (fun w => ∑' i, F i w) x) := by
  unfold I2.polyDeriv
  refine hasSum_sum fun m _ => HasSum.mul_left _ ?_
  exact (SCV.hasSum_iteratedFDeriv_of_locally_normal hU hF hle _ hx).mapL
    (ContinuousMultilinearMap.apply ℂ (fun _ => W) ℂ _)
end GlobalTheory.CanTh
