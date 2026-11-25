-- Prove2me | solution 1 for GlobalTheory.CubeExtension.pullGen_genPull
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:58:25.004451+00:00
-- url     : https://prove2.me/submissions/57d99986-2ab2-4a97-9cf2-11ea960ade46

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_CubicalExtendsAndExtendGen
import Theorems.Thm_GlobalTheory_lbGen_ext
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Semi_LB_pull_res_comp


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
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
open GlobalTheory.CubeExtension
namespace GlobalTheory.CubeExtension
theorem _root_.solution {X Y Z : Scheme.{0}} (M : LB X) (c : LB.Gen M) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LB.pullGen M _ _ (LB.genPull M c f) h = LB.genPull M c (h ≫ f) := by
  refine lbGen_ext fun j => congrArg Units.val ?_
  exact LB.pull_res_comp h f _ _ _ _ _
end GlobalTheory.CubeExtension
