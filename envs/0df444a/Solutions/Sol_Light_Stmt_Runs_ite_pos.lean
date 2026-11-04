-- Prove2me | solution 1 for Light.Stmt.Runs.ite_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:26:49.905949+00:00
-- url     : https://prove2.me/submissions/26773f2e-8007-4cfc-8bb3-4b23e79160bd

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_toNat_natCast_add_natCast
attribute [local simp] Light.toNat_natCast_add_natCast
set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Stmt.Runs
theorem _root_.solution {c : Cond} {s t : Stmt} {σ : State} {R : State → Prop} (h : s.Runs lim σ R)
    (hc : c.Holds σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
    (hs : c.Safe lim σ := by
      ( (try have := _root_.Light.Std.space_le (by assumption))
        (try have := _root_.Light.Std.const_le (by assumption))
        simp [_root_.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)) :
    (Stmt.ite c s t).Runs lim σ R :=
  ⟨⟨hs, fun _ => h.1, fun hn => absurd hc hn⟩, by simpa only [Stmt.after, if_pos hc] using h.2⟩
end Stmt.Runs
end Light
