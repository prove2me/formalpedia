-- Prove2me | solution 1 for Light.Limits.abs_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:46.660807+00:00
-- url     : https://prove2.me/submissions/1e148dca-2a5c-4455-b306-56899d3e177c

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
attribute [simp] Expr.val Expr.cost Expr.Safe Op.eval Cond.Holds Cond.cost Cond.Safe frame
namespace Light
namespace Limits
theorem _root_.solution (hw : (lim.space : ℤ) ≤ lim.word) {x : ℕ} (hx : x ≤ lim.space) :
    |(x : ℤ)| ≤ lim.word := by
  rw [abs_of_nonneg (Int.natCast_nonneg x)]
  exact le_trans (by exact_mod_cast hx) hw
end Limits
end Light
