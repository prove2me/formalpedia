-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.autFactor_mul_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:47:09.915844+00:00
-- url     : https://prove2.me/submissions/4f7f2180-7691-4ffb-ba66-88fd3fdd6a6f

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
import Theorems.Thm_GlobalTheory_TorusTransfer_mulVec_star_period
import Theorems.Thm_GlobalTheory_SiegelNormalForm_quad_add_sub
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
    (hY : (Y.map (↑) : Matrix _ _ ℂ).IsSymm) (h : Y * τ.map Complex.im = 1) (n m : Fin g → ℤ) (z l : Fin g → ℂ)
    (hl : l = τ *ᵥ ofIntVec n + ofIntVec m) :
    autFactor 0 0 τ n m z * cexp (-quad (Y.map (↑)) 0 z) =
      cexp (((Real.pi * ((n ⬝ᵥ m : ℤ) : ℝ) : ℝ) : ℂ) * I) *
        cexp (Real.pi * (z ⬝ᵥ Y.map (↑) *ᵥ star l) + Real.pi / 2 * (l ⬝ᵥ Y.map (↑) *ᵥ star l)) *
        cexp (-quad (Y.map (↑)) 0 (z + l)) := by
  have h1 := mulVec_star_period h n m
  rw [← hl] at h1
  have h2 := quad_add_sub hY 0 z l
  have h3 : l ⬝ᵥ ofIntVec n = ofIntVec n ⬝ᵥ (τ *ᵥ ofIntVec n) + ((n ⬝ᵥ m : ℤ) : ℂ) := by
    rw [hl, dotProduct_comm, dotProduct_add]
    simp [dotProduct, ofIntVec]
  have h0 : ofRealVec (0 : Fin g → ℝ) = 0 := by ext i; simp [ofRealVec]
  rw [autFactor, eC, eC, h0, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add, h1,
    eq_add_of_sub_eq h2]
  congr 1
  simp only [dotProduct_sub, dotProduct_smul, h3, smul_eq_mul, zero_dotProduct, quad, dotProduct_comm z (ofIntVec n)]
  push_cast
  ring
end GlobalTheory.TorusTransfer
