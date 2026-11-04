-- Prove2me | solution 1 for Light.Ends.skip
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:22:36.203757+00:00
-- url     : https://prove2.me/submissions/6fa2f5a0-efdc-431f-8c6f-6ed396cfcb83

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Syntax
public import Definitions.Def_Submission_ThreeSumApsp_Util_Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Tactic.Ring
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Logic

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
namespace Ends
theorem _root_.solution {σ T} {Q : State → Prop} (h : Q σ) : Ends lim P d .skip σ T Q :=
  ⟨σ, 0, .skip, Nat.zero_le _, h⟩
end Ends
end Light
