-- Prove2me | solution 1 for GroundTheory.Arith.Etale.pullbackUnitApp_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T00:07:17.479774+00:00
-- url     : https://prove2.me/submissions/2c2bd59a-756e-48cd-92ba-99aba3acaa55

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohPresheaf
import Definitions.Def_GroundTheory_ArithmeticGeometry_EtaleCompletion_QcohZariski

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Arith GroundTheory.Arith.Etale
open CategoryTheory Limits Opposite AlgebraicGeometry
universe u
variable {V T U : Scheme.{u}}
namespace GroundTheory.Arith.Etale
theorem _root_.solution (g : T ⟶ U) (N : U.Modules) {O O' : U.Opens} (i : O' ⟶ O)
    (n : Γ(N, O)) :
    pullbackUnitApp g N O' (N.presheaf.map i.op n) =
      ((Scheme.Modules.pullback g).obj N).presheaf.map ((TopologicalSpace.Opens.map g.base).map i).op
        (pullbackUnitApp g N O n) := by
  have := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app N).mapPresheaf.naturality i.op
  have h2 := congrArg (fun φ => φ.hom n) this
  simp only [AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp, Function.comp_apply] at h2
  exact h2
end GroundTheory.Arith.Etale
