-- Prove2me | solution 1 for GlobalTheory.FieldChange.tr_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:57:42.865073+00:00
-- url     : https://prove2.me/submissions/b4ac824f-52fd-42dd-8842-2f9a626c9203

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_PhiGenPf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_SectionScalarValuation
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_ExistsUniqueSamePt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SvalTwistOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SecRelationDescends
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsGenT
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_FamilyFunctionalEquationFieldChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_DVR_comp_cP
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory
open GlobalTheory.FieldChange
variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
  {F : Type} [Field F] [Algebra (FractionRing R) F]
namespace GlobalTheory.FieldChange
theorem _root_.solution (φ : TF (R := R) F ⟶ T) (mu : D.X) :
    φ ▷ D.P.A ≫ trT D (toUnit T ≫ D.c mu) = DegPre.trF D F mu ≫ φ ▷ D.P.A := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [trT, DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerRight_snd, trT, DegPre.trF, lift_snd, lift_snd]
    refine (MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (fst _ _ ≫ DVR.cP D _ mu)).trans ?_
    rw [whiskerRight_snd, DVR.comp_cP, DVR.comp_cP]; rfl
end GlobalTheory.FieldChange
