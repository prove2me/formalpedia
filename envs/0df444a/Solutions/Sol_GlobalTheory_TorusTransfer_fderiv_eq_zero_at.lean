-- Prove2me | solution 1 for GlobalTheory.TorusTransfer.fderiv_eq_zero_at
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:29:14.469085+00:00
-- url     : https://prove2.me/submissions/e8b57ec4-62c2-44e1-aaa6-ab1c56b7d02f

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
import Theorems.Thm_GlobalTheory_top_le_preimage_comp
import Theorems.Thm_P2M_GlobalTheory_valAt__comp_7a5ff8fa895a
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_I2_DimB_ex_add
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
variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)
namespace GlobalTheory.TorusTransfer
theorem _root_.solution (w : Fin g → ℂ)
    (hw : ∀ (U : A.left.Opens) (f : Γ(A.left, U)), ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U →
      fderiv ℂ (fun z => valAt' (u.ex z).left U f) 0 w = 0)
    (z₀ : Fin g → ℂ) (U : A.left.Opens) (f : Γ(A.left, U)) (h : ⊤ ≤ (u.ex z₀).left ⁻¹ᵁ U) :
    fderiv ℂ (fun z => valAt' (u.ex z).left U f) z₀ w = 0 := by
  let T : A ⟶ A := (toUnit A ≫ u.ex z₀) * 𝟙 A
  have hT : ∀ z, (u.ex z).left ≫ T.left = (u.ex (z₀ + z)).left := fun z => by
    rw [← Over.comp_left, u.ex_add]
    congr 1
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, toUnit_unique (u.ex z ≫ toUnit A) (𝟙 _),
      Category.id_comp]
  have h1 := hw (T.left ⁻¹ᵁ U) ((T.left.app U).hom f)
    (by rw [← top_le_preimage_comp, hT, add_zero]; exact h)
  simp only [valAt'_comp, hT] at h1
  rw [fderiv_comp_add_left (f := fun z => valAt' (u.ex z).left U f), add_zero] at h1
  exact h1
end GlobalTheory.TorusTransfer
