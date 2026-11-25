-- Prove2me | solution 1 for GlobalTheory.CanTh.polyDeriv_congr_of_eventuallyEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:01:02.830791+00:00
-- url     : https://prove2.me/submissions/2e819bab-3c78-4cd2-b093-b26fe1a74e79

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
omit [FiniteDimensional ℂ W]
namespace GlobalTheory.CanTh
theorem _root_.solution (P : MvPolynomial σ ℂ) (u : σ → W) {F G : W → ℂ} {x : W}
    (h : F =ᶠ[𝓝 x] G) : I2.polyDeriv P u F x = I2.polyDeriv P u G x := by
  unfold I2.polyDeriv
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [(h.iteratedFDeriv ℂ _).eq_of_nhds]
end GlobalTheory.CanTh
