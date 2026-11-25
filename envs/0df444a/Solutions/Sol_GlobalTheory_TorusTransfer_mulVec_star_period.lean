-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.mulVec_star_period
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:20:26.915461+00:00
-- url     : https://prove2.me/submissions/2f16319d-21a5-4aea-ba86-2d2fb42e32f4

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ThetaQuasiPeriods_Transl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_EqZeroOfSemicharacterMultiplier
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_IsUnitOfLagrangian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TopLePreimageOfValAtNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsUniquePointOfRingHom
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsTestFunctionsSubsetOfMemNhds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_ExistsEtaleCoordsVanishing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_TangentBijectionOfValues
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_LevelThreeSeparatesPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_FderivEqZeroOfAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ToricGeometry_PolarisedTorusAlgebraicOfParts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_EqZeroOfFderivEqZero
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
import Theorems.Thm_GlobalTheory_thetaLevelBasis_apply
import Theorems.Thm_GlobalTheory_thetaLevelCharBasis_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk
attribute [local simp] GlobalTheory.thetaLevelBasis_apply
attribute [local simp] GlobalTheory.thetaLevelCharBasis_apply



set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real CategoryTheory.Obj
open GlobalTheory GlobalTheory.TorusTransfer
open SiegelNormalForm
variable {g : ℕ}
namespace GlobalTheory.TorusTransfer
theorem _root_.solution {Y : Matrix (Fin g) (Fin g) ℝ} {τ : Matrix (Fin g) (Fin g) ℂ}
    (h : Y * τ.map Complex.im = 1) (n m : Fin g → ℤ) :
    (Y.map (↑) : Matrix _ _ ℂ) *ᵥ star (τ *ᵥ ofIntVec n + ofIntVec m) =
      Y.map (↑) *ᵥ (τ *ᵥ ofIntVec n + ofIntVec m) - (2 * I) • ofIntVec n := by
  have h1 : star (τ *ᵥ ofIntVec n + ofIntVec m) = (τ *ᵥ ofIntVec n + ofIntVec m) -
      (2 * I) • (((τ.map Complex.im).map ((↑) : ℝ → ℂ)) *ᵥ ofIntVec n) := by
    ext i
    apply Complex.ext
    · simp [Matrix.mulVec, dotProduct, ofIntVec]
    · simp [Matrix.mulVec, dotProduct, ofIntVec]
      ring
  have h2 : (Y.map ((↑) : ℝ → ℂ)) * (τ.map Complex.im).map ((↑) : ℝ → ℂ) = 1 := by
    have := congrArg (fun M : Matrix (Fin g) (Fin g) ℝ => M.map Complex.ofRealHom) h
    simp only [Matrix.map_mul] at this
    rw [Matrix.map_one _ (map_zero _) (map_one _)] at this
    exact this
  rw [h1, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
end GlobalTheory.TorusTransfer
