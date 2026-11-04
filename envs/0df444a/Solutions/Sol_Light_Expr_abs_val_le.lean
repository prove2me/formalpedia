-- Prove2me | solution 1 for Light.Expr.abs_val_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:14:01.465568+00:00
-- url     : https://prove2.me/submissions/514c8d17-6be7-4cef-ab39-9f0c76b6adcf

import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
import Definitions.Def_Submission_ThreeSumApsp_Util_List
import Mathlib.Tactic.SplitIfs
import Definitions.Def_Submission_ThreeSumApsp_Lang_RunsStayInLimits

set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Expr
theorem _root_.solution {σ : State} (hσ : σ.Bounded lim) :
    ∀ e : Expr, e.Safe lim σ → |e.val σ| ≤ lim.word
  | .const n, h => by
    rw [Expr.val, abs_of_nonneg (Int.natCast_nonneg n)]
    exact h
  | .var x, _ => hσ.1 x
  | .op _ _ _, h => h.2.2
  | .load _, _ => hσ.2 _
end Expr
end Light
