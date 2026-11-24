-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:32:50.293673+00:00
-- url     : https://prove2.me/submissions/133c1cb3-e8ec-47c6-9aba-87a0a082fca4

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

namespace GroundTheory.Arith.SchemeCoh
theorem _root_.solution {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ (0 : Fin (n + 2)).succAbove = i := by
  funext a
  simp
end GroundTheory.Arith.SchemeCoh
