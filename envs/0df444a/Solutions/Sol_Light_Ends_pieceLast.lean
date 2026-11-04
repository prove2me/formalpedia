-- Prove2me | solution 1 for Light.Ends.pieceLast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:28:08.549484+00:00
-- url     : https://prove2.me/submissions/b3476eba-f97b-4021-a72b-bb2bc27341ea

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_mono
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ : State} {T T₁ : ℕ} {s : Stmt} {R Q : State → Prop} (h : Ends lim P d s σ T₁ R)
    (rest : ∀ σ', R σ' → Q σ')
    (hT : T₁ ≤ T := by
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
  h.mono hT rest
end Ends
end Light
