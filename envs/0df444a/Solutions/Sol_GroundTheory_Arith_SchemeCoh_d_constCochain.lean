-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.d_constCochain
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:02.3499+00:00
-- url     : https://prove2.me/submissions/e440b09c-655b-4236-920f-993d871b5b90

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_InjectiveCech
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_Cartan
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_zero_apply

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
variable {ι : Type w} (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {V : Opens X} (hUV : ∀ a, U a ≤ V) (s : P.obj (op V)) :
    d P U 0 (constCochain P U hUV s) = 0 := by
  funext i
  rw [d_zero_apply]
  simp only [constCochain, res_res, sub_self]
  rfl
end GroundTheory.Arith.SchemeCoh
