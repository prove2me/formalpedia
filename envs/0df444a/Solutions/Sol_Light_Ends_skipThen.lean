-- Prove2me | solution 1 for Light.Ends.skipThen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:27:30.472197+00:00
-- url     : https://prove2.me/submissions/a590d91c-503a-46b2-b3f4-fea8e4bacc7b

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic
public import Mathlib.Algebra.Order.Group.Abs
public import Mathlib.Algebra.Order.Ring.Abs
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Theorems.Thm_Light_Ends_skip


set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ : State} {T : ℕ} {s : Stmt} {Q : State → Prop} (h : Ends lim P d s σ T Q) :
    Ends lim P d (.skip ;; s) σ T Q :=
  Ends.seq 0 T (Ends.skip h) (by omega)
end Ends
end Light
