-- Prove2me | solution 1 for GlobalTheory.AbLaw.CubeGen.one_left_fst
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:53:00.178826+00:00
-- url     : https://prove2.me/submissions/bc418ec6-634c-479a-89d8-dcfa7716ad5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RosVal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_TrivPullCompIff
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_isGrpPullback_pullback


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.AbLaw.CubeGen
variable {S : Scheme.{0}} (A : Over S) [GrpObj A]
variable {A}
namespace GlobalTheory.AbLaw.CubeGen
theorem _root_.solution {S' : Scheme.{0}} (f : S' ⟶ S) (T : Over S') :
    (1 : T ⟶ (Over.pullback f).obj A).left ≫ pullback.fst A.hom f = (T.hom ≫ f) ≫ η[A].left :=
  congrArg (fun z => z.left) (map_one (pushHom (isGrpPullback_pullback A f) T))
end GlobalTheory.AbLaw.CubeGen
