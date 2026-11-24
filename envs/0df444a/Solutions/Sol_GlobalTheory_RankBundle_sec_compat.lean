-- Prove2me | solution 1 for GlobalTheory.RankBundle.sec_compat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:48:50.813554+00:00
-- url     : https://prove2.me/submissions/25f85375-af5a-47ba-8163-79d95d54d0c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsRankOneBundle
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_IsCub_compat


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RankBundle
variable {X : Scheme.{0}}
namespace GlobalTheory.RankBundle
theorem _root_.solution {N : LB X} (s : LB.Sec N) (x : X) {k k' : N.ι} (hk : x ∈ N.U k) (hk' : x ∈ N.U k') :
    gs (𝟙 X) x (N.U k) (s.f k) = (gm (𝟙 X) x (N.U k ⊓ N.U k') (N.g k k')).val * gs (𝟙 X) x (N.U k') (s.f k') := by
  have hm : x ∈ N.U k ⊓ N.U k' := ⟨hk, hk'⟩
  exact (gs_res (𝟙 X) x _ hm _).symm.trans ((congrArg (gs (𝟙 X) x _) (s.compat k k')).trans
    ((gs_mul (𝟙 X) x _ hm _ _).trans (congrArg₂ (· * ·) (gs_unit (𝟙 X) x _ hm _) (gs_res (𝟙 X) x _ hm _))))
end GlobalTheory.RankBundle
