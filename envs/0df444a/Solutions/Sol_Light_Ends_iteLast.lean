-- Prove2me | solution 1 for Light.Ends.iteLast
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:29:12.04974+00:00
-- url     : https://prove2.me/submissions/a790e1bc-a86d-4b96-b77e-3c5b4fde33ae

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ : State} {T : ℕ} {c : Cond} {s₁ s₂ : Stmt} {Q : State → Prop}
    (h₁ : c.Holds σ → Ends lim P d s₁ σ (T - (c.cost + 1)) Q) (h₂ : ¬c.Holds σ → Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by
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
    Ends lim P d (.ite c s₁ s₂) σ T Q :=
  Ends.ite _ hs h₁ h₂ (by omega)
end Ends
end Light
