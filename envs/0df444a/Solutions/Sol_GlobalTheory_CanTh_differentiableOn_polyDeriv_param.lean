-- Prove2me | solution 1 for GlobalTheory.CanTh.differentiableOn_polyDeriv_param
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:50:25.377227+00:00
-- url     : https://prove2.me/submissions/3f0c88d8-1e2b-455d-81f2-3269cebf13e0

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
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_polyDeriv_snd

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
theorem _root_.solution {F : B × W → ℂ} {V : Set B} (hV : IsOpen V)
    (hF : DifferentiableOn ℂ F (V ×ˢ Set.univ)) (P : MvPolynomial σ ℂ) (u : σ → W) (x : W) :
    DifferentiableOn ℂ (fun s : B => I2.polyDeriv P u (fun w => F (s, w)) x) V :=
  (differentiableOn_polyDeriv_snd (hV.prod isOpen_univ) hF P u).comp (f := fun s => (s, x))
    (by fun_prop) fun _ hs => ⟨hs, trivial⟩
end GlobalTheory.CanTh
