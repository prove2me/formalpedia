-- Prove2me | solution 1 for GlobalTheory.FieldChange.fam_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:56:27.276261+00:00
-- url     : https://prove2.me/submissions/1d0d2456-fbda-47d5-9e7c-cb5003045142

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
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_symm
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
theorem _root_.solution (φ : TF (R := R) F ⟶ T) (α : D.X) :
    DegPre.famφ D F α = fun i => (φ ▷ D.P.A).left ≫ famφT D T α i := by
  have e₀ : φ ▷ D.P.A ≫ snd T D.P.A = snd _ _ := whiskerRight_snd _ _
  have e₂ : φ ▷ D.P.A ≫ DVR.cP D _ α = DVR.cP D _ α := DVR.comp_cP D _ α
  funext i
  fin_cases i
  · exact (congrArg (fun q => q.left) e₀).symm
  · refine (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left)
      ((MonObj.comp_mul (φ ▷ D.P.A) (snd T D.P.A) (DVR.cP D _ α)).trans ?_)).symm
    rw [e₀, e₂]; rfl
  · exact (congrArg (fun q => q.left) e₂).symm
  · exact (congrArg (fun q : DegPre.BF D F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (φ ▷ D.P.A))).symm
end GlobalTheory.FieldChange
