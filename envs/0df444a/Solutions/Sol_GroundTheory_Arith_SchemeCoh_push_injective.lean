-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.push_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:19.947379+00:00
-- url     : https://prove2.me/submissions/1f2ba7b5-4412-42c6-acd7-205113be8c25

import Mathlib
import Definitions.Def_GroundTheory_ArithmeticGeometry_SchemeCohomology_ConsCompSuccAboveZero

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
theorem _root_.solution {P' : (Opens X)ᵒᵖ ⥤ AddCommGrpCat.{u}} (φ : P ⟶ P') (n : ℕ)
    (h : ∀ i : Fin (n + 1) → ι, Function.Injective (φ.app (op (inter U i)))) :
    Function.Injective (push U φ n) := fun _ _ hστ =>
  funext fun i => h i (congrFun hστ i)
end GroundTheory.Arith.SchemeCoh
