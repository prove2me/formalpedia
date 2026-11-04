-- Prove2me | solution 1 for Light.Ends.setVal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:30:47.828332+00:00
-- url     : https://prove2.me/submissions/9f488f38-a69a-4c6d-a879-6ac1fbbb834b

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_Ends_set
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : State → Prop}
namespace Light
namespace Ends
theorem _root_.solution {loc : ℕ → ℤ} {x : ℕ} {e : Expr} (z : ℤ) (h : Q ⟨Function.update loc x z, μ⟩)
    (he : e.Gives lim ⟨loc, μ⟩ z := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hT : e.cost + 1 ≤ T := by
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
    Ends lim P d (.set x e) ⟨loc, μ⟩ T Q :=
  Ends.set he.1 hT (he.2 ▸ h)
end Ends
end Light
