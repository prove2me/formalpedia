-- Prove2me | solution 1 for GlobalTheory.SemiRigid.isMonHom_of_axes
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:28:45.808144+00:00
-- url     : https://prove2.me/submissions/19f8e6e3-62e1-445e-962b-ff03b9058251

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_AbelianSchemeQuotients_IsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HomBaseChangeBijectiveOfLeNilradical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_LocallyOfFinitePresentationDiagMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_BijectiveRestrictPointsOfEtaleOfHenselian
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_OneTmulNeZeroOfDomain
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsNoetherianModelOfSmooth
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIsoAppTopOfIsAffine
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_EqCompSectionOfSurjectiveAppTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SurjectiveAppOfIsAbelianScheme
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExtOfForallQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GeometricallyConnectedOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_GroupRingHomConstOfLaurent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsTorusAndQuotientHom
import Theorems.Thm_GlobalTheory_GroupRingConst_powChar_apply
import Theorems.Thm_GlobalTheory_GroupRingConst_pt_single
import Theorems.Thm_GlobalTheory_restrictPoints_val
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.GroupRingConst.powChar_apply
attribute [local simp] GlobalTheory.GroupRingConst.pt_single
attribute [local simp] GlobalTheory.restrictPoints_val



set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Semi.Rosenlicht
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.SemiRigid
open SplitTorus
variable {K : Type} [Field K]
namespace GlobalTheory.SemiRigid
theorem _root_.solution {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : G ⊗ G ⟶ H, lift (𝟙 G) 1 ≫ f = 1 → lift 1 (𝟙 G) ≫ f = 1 → f = 1)
    (φ : G ⟶ H) (hφ : η[G] ≫ φ = η[H]) : IsMonHom φ := by
  have h1 : (1 : G ⟶ G) ≫ φ = 1 := by
    rw [Hom.one_def, Category.assoc, hφ, Hom.one_def]
  have := h (((fst G G * snd G G) ≫ φ) * ((fst G G ≫ φ) * (snd G G ≫ φ))⁻¹)
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      _root_.mul_one, mul_inv_cancel])
    (by simp only [MonObj.comp_mul, GrpObj.comp_inv, ← Category.assoc, lift_fst, lift_snd, h1,
      _root_.one_mul, mul_inv_cancel])
  rw [mul_inv_eq_one, Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
  refine ⟨hφ, ?_⟩
  rw [this]
  congr 1
end GlobalTheory.SemiRigid
