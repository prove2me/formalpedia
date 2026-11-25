-- Prove2me | solution 1 for GlobalTheory.CanTh.differentiableOn_thTerm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:14.414736+00:00
-- url     : https://prove2.me/submissions/896a015d-b456-4146-98ba-a6048af72997

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
import Theorems.Thm_GlobalTheory_CanTh_thTerm_eq_thetaTerm
import Theorems.Thm_GlobalTheory_differentiable_thetaTerm_prod
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
variable {g : ℕ}
variable {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W]
namespace GlobalTheory.CanTh
theorem _root_.solution {U : Set W} {T : W → Matrix (Fin g) (Fin g) ℂ}
    {Z : W → Fin g → ℂ} (hT : ∀ i j, DifferentiableOn ℂ (fun w => T w i j) U)
    (hZ : DifferentiableOn ℂ Z U) (a b : Fin g → ℝ) (m : Fin g → ℤ) :
    DifferentiableOn ℂ (fun w => thTerm (T w) a b (Z w) m) U := by
  simp only [thTerm_eq_thetaTerm]
  exact (differentiable_thetaTerm_prod a b m).comp_differentiableOn
    (f := fun w => (Z w, fun i j => T w i j))
    (hZ.prodMk (differentiableOn_pi.2 fun i => differentiableOn_pi.2 fun j => hT i j))
end GlobalTheory.CanTh
