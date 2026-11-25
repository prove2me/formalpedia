-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.pullbackUnitApp_smul_resM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T00:49:10.866831+00:00
-- url     : https://prove2.me/submissions/c7ef3834-49f3-47e2-86a9-ed13b15250bd

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InvertibleDual
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ProjectiveCohomology_ImmersionPullback
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_pullbackUnitApp_smul
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_bijective
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_comp_hom
import Theorems.Thm_GroundTheory_Arith_Etale_pullbackUnitApp_res


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
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace Limits MonoidalCategory
open GroundTheory.Arith.Etale (pullbackUnitApp pullbackUnitApp_res pullbackUnitApp_comp
  pullbackUnitApp_comp_hom pullbackUnitApp_bijective)
universe u
noncomputable section
variable {Y Z : Scheme.{u}}
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution (j : Y ⟶ Z) (N : Z.Modules) {O V : Z.Opens} (h : V ≤ O)
    (r : ringOn Z V) (t : Γ(N, O)) :
    pullbackUnitApp j N V (r • resM ((preMod Z).obj N) h t) =
      appR j V r • resM ((preMod Y).obj ((Scheme.Modules.pullback j).obj N))
        ((Opens.map j.base).monotone h) (pullbackUnitApp j N O t) := by
  have e1 := pullbackUnitApp_smul j N V r (resM ((preMod Z).obj N) h t)
  have e2 := pullbackUnitApp_res j N (homOfLE h) t
  exact e1.trans (congrArg _ e2)
end GroundTheory.Arith.SchemeCoh
