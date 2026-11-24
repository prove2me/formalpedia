-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.ev_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:47:09.949092+00:00
-- url     : https://prove2.me/submissions/5c8b9fa7-c6a7-4372-a6bb-d79a9deb3b29

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
variable (A : X → AddCommGrpCat.{u})
attribute [local semireducible] inter

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {V W : Opens X} (h : V ≤ W) (s : (discPresheaf A).obj (op W)) (x : X) (hx : x ∈ V) :
    ev A x hx (res (discPresheaf A) h s) = ev A x (h hx) s := rfl
end GroundTheory.Arith.SchemeCoh
