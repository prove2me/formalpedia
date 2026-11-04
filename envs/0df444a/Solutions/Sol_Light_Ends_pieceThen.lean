-- Prove2me | solution 1 for Light.Ends.pieceThen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:28:28.246722+00:00
-- url     : https://prove2.me/submissions/460a956c-a2fb-4ce5-98e5-21cfe0e66844

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_next
public import Theorems.Thm_Light_Ends_mono
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ : State} {T T₁ : ℕ} {s₁ s₂ : Stmt} {R Q : State → Prop} (h : Ends lim P d s₁ σ T₁ R)
    (rest : ∀ σ', R σ' → Ends lim P d s₂ σ' (T - T₁) Q)
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
    Ends lim P d (_root_.Light.Stmt.seq s₁ s₂) σ T Q :=
  Ends.next T₁ (h.mono le_rfl rest) hT
end Ends
end Light
