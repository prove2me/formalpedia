-- Prove2me | solution 1 for GlobalTheory.EquivDesc.mem_chart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:23:26.435862+00:00
-- url     : https://prove2.me/submissions/c3478d9b-be68-4342-b56c-2b1f1ed8a3ad

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
namespace GlobalTheory.EquivDesc
theorem _root_.solution {T : Over S} (t : T ⟶ H) (x : T ⟶ G) (z : T.left) {k₁ k₂ : L.ι}
    (h₁ : ((t ≫ i) * x).left z ∈ L.U k₁) (h₂ : x.left z ∈ L.U k₂) :
    (lift t x).left z ∈ LB.wchart L (actφ i) ![k₁, k₂] := Set.mem_iInter.2 fun k => by
  fin_cases k
  · rw [← lift_actφ_zero] at h₁; exact h₁
  · rw [← lift_actφ_one (i := i) t] at h₂; exact h₂
end GlobalTheory.EquivDesc
