-- Prove2me | solution 1 for Light.Cond.holds_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:43.014592+00:00
-- url     : https://prove2.me/submissions/33b88aeb-833d-48aa-a580-acb00f00e70a

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Cond
theorem _root_.solution {σ : State} {a b : Expr} : (a ≤' b).Holds σ ↔ a.val σ ≤ b.val σ :=
  Int.lt_add_one_iff
end Cond
end Light
