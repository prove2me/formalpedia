-- Prove2me | solution 1 for Light.Ends.iteIffThen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:29:46.653+00:00
-- url     : https://prove2.me/submissions/d5186523-4133-4229-b1e1-3f0a7854baf0

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_iteThen
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ s : Stmt} {Q : State → Prop} (p : Prop)
    (h₁ : p → Ends lim P d (_root_.Light.Stmt.seq s₁ s) σ (T - (c.cost + 1)) Q)
    (h₂ : ¬p → Ends lim P d (_root_.Light.Stmt.seq s₂ s) σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ ∧ (c.Holds σ ↔ p) := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hT : c.cost + 1 ≤ T := by
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
    Ends lim P d (_root_.Light.Stmt.seq (.ite c s₁ s₂) s) σ T Q :=
  Ends.iteThen (fun hc => h₁ (hs.2.1 hc)) (fun hc => h₂ fun hp => hc (hs.2.2 hp)) hs.1 hT
end Ends
end Light
