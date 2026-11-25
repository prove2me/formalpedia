-- Prove2me | solution 1 for GlobalTheory.CanTh.canTh_add_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:54:11.078803+00:00
-- url     : https://prove2.me/submissions/8be3b5ad-ddb8-4d97-8f10-6392409b945b

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
import Theorems.Thm_GlobalTheory_CanTh_thetaChar_eq_theta
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
import Theorems.Thm_ReciprocityTheory_PTheta_thetaIntChar_holds
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
variable {τ : Matrix (Fin g) (Fin g) ℂ}
namespace GlobalTheory.CanTh
theorem _root_.solution (τ : Matrix (Fin g) (Fin g) ℂ) (a b : Fin g → ℝ) (n m : Fin g → ℤ)
    (ζ : Fin g → ℂ) :
    canTh τ (a + fun i => (n i : ℝ)) (b + fun i => (m i : ℝ)) ζ =
      cexp (2 * π * I * ((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ)) * canTh τ a b ζ := by
  have e : ofRealVec a ⬝ᵥ ofIntVec m = ((a ⬝ᵥ fun i => (m i : ℝ) : ℝ) : ℂ) := by
    simp [dotProduct, ofRealVec, ofIntVec]
  rw [canTh, canTh, thetaChar_eq_theta, thetaChar_eq_theta, thetaIntChar_holds, e, eC]
  ring
end GlobalTheory.CanTh
