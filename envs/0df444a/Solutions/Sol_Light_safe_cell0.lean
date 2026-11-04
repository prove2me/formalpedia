-- Prove2me | solution 1 for Light.safe_cell0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:30:41.41129+00:00
-- url     : https://prove2.me/submissions/decccf55-5a41-4ff2-a553-8a4af1c4f6a1

import Definitions.Def_Submission_ThreeSumApsp_Lang_RowMajor
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Definitions.Def_Submission_ThreeSumApsp_Lang_ToMachine
import Definitions.Def_Submission_ThreeSumApsp_Machine_Realized
import Definitions.Def_Submission_ThreeSumApsp_Util_Flag
import Definitions.Def_Submission_ThreeSumApsp_Lang_TopProcedure
set_option autoImplicit false
section
open Light
open ThreeSumApsp ThreeSumApsp.WordRam
variable {lim : Limits} {P : Program} {d : ℕ}
variable {Q : EndStatement.Problem} (x : Bounded Q)
namespace Light
theorem _root_.solution {lim : Limits} {σ : State} (h0 : 0 ≤ lim.word) (h1 : 1 ≤ lim.space) : (M (k 0)).Safe lim σ :=
  by
  simp only [_root_.Light.Expr.Safe, _root_.Light.Expr.val, _root_.Light.Expr.cost, _root_.Light.Op.eval,
    _root_.Light.Cond.Holds, _root_.Light.Cond.cost, _root_.Light.Cond.Safe, _root_.Function.update_apply,
    _root_.reduceIte, _root_.true_and, _root_.and_true, _root_.Nat.reduceEqDiff, _root_.Nat.cast_ofNat,
    _root_.Nat.cast_zero, _root_.Nat.cast_one, ]
  exact ⟨h0, le_rfl, by omega⟩
end Light
