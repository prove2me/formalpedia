-- Prove2me | solution 1 for GlobalTheory.boxRigIsGen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:43:38.145806+00:00
-- url     : https://prove2.me/submissions/15948305-b5ae-49ab-800d-3fcc7e233baf

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_MapsAtLeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_ChartPullbacks_GeneratorPullback_PullAlong
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_LcgLinCombEqProd
import Theorems.Thm_GlobalTheory_isGen_boxGen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Out_LBxP_isGen_pullAlong


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (S : Scheme.{0}) : BoxRigIsGenSt (S := S) := by
  intro G' G _ _ _ _ j p L r hL hr
  refine isGen_boxGen _ _ _ _ _ (fun i => ?_)
  have := p.hom i
  exact LBxP.isGen_pullAlong L (p.pr i).left (𝟙 _) (fun _ : PUnit => eSec G)
    (fun _ => 1) (fun _ => eSec G') (fun _ => (CubeMap.ofHom (p.pr i)).e_comm) r hr
end GlobalTheory
