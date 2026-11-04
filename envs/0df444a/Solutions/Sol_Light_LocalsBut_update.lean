-- Prove2me | solution 1 for Light.LocalsBut.update
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:15.724929+00:00
-- url     : https://prove2.me/submissions/6a59834a-d71a-4bb2-ab99-981e96c747f9

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
namespace Light
namespace LocalsBut
theorem _root_.solution (h : LocalsBut xs l loc) (x : ℕ) (z : ℤ) :
    LocalsBut xs (setLocal l x z) (Function.update loc x z) := by
  intro y hy
  rw [frame_setLocal, Function.update_apply, h y hy]
end LocalsBut
end Light
