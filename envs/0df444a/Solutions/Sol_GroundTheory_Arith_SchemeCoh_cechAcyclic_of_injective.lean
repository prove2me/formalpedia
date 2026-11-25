-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cechAcyclic_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:04:22.092806+00:00
-- url     : https://prove2.me/submissions/959eb57b-0daa-4f40-8cdf-5978dcbc83ae

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_CechAcyclic_of_retract
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_cechAcyclic_discPresheaf


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.SchemeCoh
open CategoryTheory Opposite TopologicalSpace Limits
universe w u
variable {X : TopCat.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I]
    {ι : Type w} (U : ι → Opens X) : CechAcyclic I.obj U := by
  let r := Injective.factorThru (𝟙 I) (toGermSheaf I)
  have hr : toGermSheaf I ≫ r = 𝟙 I := Injective.comp_factorThru _ _
  have hr' : toGerms I ≫ r.hom = 𝟙 I.obj := congrArg (fun f => f.hom) hr
  exact CechAcyclic.of_retract U (toGerms I) r.hom hr' (cechAcyclic_discPresheaf U _)
end GroundTheory.Arith.SchemeCoh
