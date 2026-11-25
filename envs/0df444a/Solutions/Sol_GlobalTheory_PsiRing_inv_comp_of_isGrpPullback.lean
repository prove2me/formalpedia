-- Prove2me | solution 1 for GlobalTheory.PsiRing.inv_comp_of_isGrpPullback
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:18:18.981006+00:00
-- url     : https://prove2.me/submissions/5b3afd49-886f-48f6-a234-f84f1fb9b729

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ValEqOfAppInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_TauBimultOfIsPullDeg
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_CubicalSymmetryTransport
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SecCmp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_PsiEvenDescendBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
noncomputable section
open GlobalTheory GlobalTheory.PsiRing
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
  {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)}
namespace GlobalTheory.PsiRing
theorem _root_.solution (gp : IsGrpPullback D'.P.A D.P.A (spMap φ) β) :
    (ι[D'.P.A]).left ≫ β = β ≫ (ι[D.P.A]).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom gp D'.P.A) (𝟙 _))
  rw [Hom.inv_def, Hom.inv_def, Category.id_comp] at e
  refine e.trans ?_
  show ((𝟙 D'.P.A : D'.P.A ⟶ D'.P.A).left ≫ β) ≫ _ = _
  rw [Over.id_left, Category.id_comp]
end GlobalTheory.PsiRing
