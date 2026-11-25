-- Prove2me | solution 1 for GlobalTheory.LN.Cmp.one_fstG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:02:16.127095+00:00
-- url     : https://prove2.me/submissions/b6770c2d-a9f4-4e4f-9915-012981c0ed04

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_WCompat
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_SameB
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PsiScal
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_ExistsUniquePartner
import Theorems.Thm_GlobalTheory_UU_one_left_comp
import Theorems.Thm_GlobalTheory_UU_toBase_mul_pullback


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
noncomputable section
open GlobalTheory GlobalTheory.LN
open GlobalTheory.UU
variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {I : Ideal R} {I' : Ideal V}
  {D : DegPre R} {D' : DegPre V} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing V)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] {G' : Over (Spec (CommRingCat.of V))} [GrpObj G'] [IsCommMonObj G']
open GlobalTheory.LN.Cmp
variable {φ : R →+* V} {U : PreU I D A G} {U' : PreU I' D' A' G'} {F : G'.left ⟶ G.left}
namespace GlobalTheory.LN.Cmp
theorem _root_.solution (I : Ideal R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G]
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (1 : T ⟶ thickObj R I e G).left ≫ (fstG I e G).left = (T.hom ≫ thick R I e) ≫ eSec G :=
  one_left_comp (toBase_mul_pullback G (thick R I e)) T
end GlobalTheory.LN.Cmp
