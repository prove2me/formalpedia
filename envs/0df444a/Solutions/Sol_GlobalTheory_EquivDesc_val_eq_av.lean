-- Prove2me | solution 1 for GlobalTheory.EquivDesc.val_eq_av
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:26:32.53923+00:00
-- url     : https://prove2.me/submissions/24783a48-b23d-4420-91d8-20954c5d27e0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_PointEqOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_InvariantFunctionsDescend
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsStalkHom
import Theorems.Thm_P2M_GlobalTheory_EquivDesc_lift_act__zero_b11de49948e9
import Theorems.Thm_P2M_GlobalTheory_EquivDesc_lift_act__one_76b398679955
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_val_of


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU TopologicalSpace
noncomputable section
open GlobalTheory GlobalTheory.EquivDesc
variable {S : Scheme.{0}}
variable {G H : Over S} [GrpObj G] [GrpObj H] {i : H ⟶ G} {L : LB G.left}
variable {a : LB.Gen (LB.LinComb L (actφ i) ![1, -1])}
namespace GlobalTheory.EquivDesc
theorem _root_.solution {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) (J) :
    val a (lift t x).left z J = av a t x z (J ((t ≫ i) * x).left) (J x.left) :=
  val_of a _ z J _ fun k => by
    fin_cases k
    · exact congrArg J (lift_actφ_zero t x)
    · exact congrArg J (lift_actφ_one t x)
end GlobalTheory.EquivDesc
