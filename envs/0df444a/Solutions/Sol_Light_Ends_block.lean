-- Prove2me | solution 1 for Light.Ends.block
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:00:59.495642+00:00
-- url     : https://prove2.me/submissions/5e631a9d-9d7b-4b66-85f8-99a624064562

import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_WeightedCache3SUM_Alias_15c25ca96fda9d90
set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {s : Stmt} {σ : State} {T : ℕ} {Q : State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by
      first
      | ( simp only [_root_.Light.Stmt.blockCost, _root_.Light.Cond.cost, _root_.Light.Expr.cost, _root_.List.map_cons,
            _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
          first
          | omega
          | (ring_nf; omega))
      | omega
      |
        (simp [] <;>
            first
            | omega
            | (ring_nf; omega))) :
    Ends lim P d s σ T Q :=
  Ends.of_blockSafe h.1 hT h.2
end Ends
end Light
