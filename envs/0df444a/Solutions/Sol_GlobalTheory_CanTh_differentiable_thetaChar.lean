-- Prove2me | solution 1 for GlobalTheory.CanTh.differentiable_thetaChar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:55:05.007444+00:00
-- url     : https://prove2.me/submissions/b6afb8d8-2a29-40c9-9ee9-a9fcf235b2b1

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
import Theorems.Thm_GlobalTheory_CanTh_differentiableOn_thetaChar

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
variable {g : ℕ}
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CanTh
theorem _root_.solution {τ : Matrix (Fin g) (Fin g) ℂ} (hτ : τ ∈ ThetaDomain (Fin g))
    (a b : Fin g → ℝ) :
    Differentiable ℂ (thetaChar τ (fun i => (a i : ℂ)) (fun i => (b i : ℂ))) :=
  differentiableOn_univ.1 (differentiableOn_thetaChar (T := fun _ => τ) (Z := id)
    (fun _ _ => differentiableOn_const _) differentiableOn_id (fun _ _ => hτ) a b)
end GlobalTheory.CanTh
