-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.push_d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:42:10.298464+00:00
-- url     : https://prove2.me/submissions/cfc0935f-472a-4818-9de0-c8b968d94d95

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_d_apply
import Theorems.Thm_GroundTheory_Arith_SchemeCoh_app_res

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
open CategoryTheory Opposite TopologicalSpace
universe w u v
variable {X : TopCat.{u}} {ι : Type w}
variable (P : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}) (U : ι → Opens X)
variable {P}
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ) (σ : Cochain P U n) :
    push U φ (n + 1) (d P U n σ) = d P' U n (push U φ n σ) := by
  funext i
  simp only [push, AddMonoidHom.coe_mk, ZeroHom.coe_mk, d_apply, map_sum, map_zsmul, app_res]
end GroundTheory.Arith.SchemeCoh
