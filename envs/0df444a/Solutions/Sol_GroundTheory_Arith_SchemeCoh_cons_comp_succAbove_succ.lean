-- Prove2me | solution 1 for GroundTheory.Arith.SchemeCoh.cons_comp_succAbove_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:36.681453+00:00
-- url     : https://prove2.me/submissions/0241201e-409f-4c07-be64-0596b9c7ec97

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
theorem _root_.solution {n : ℕ} (c : ι) (i : Fin (n + 1) → ι) (k : Fin (n + 1)) :
    (Fin.cons c i : Fin (n + 2) → ι) ∘ k.succ.succAbove = Fin.cons c (i ∘ k.succAbove) := by
  funext a
  cases a using Fin.cases with
  | zero => simp
  | succ a => simp
end GroundTheory.Arith.SchemeCoh
