-- Prove2me | solution 1 for Light.LocalsBut.eq_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:49.587011+00:00
-- url     : https://prove2.me/submissions/6c29dd42-0178-4d90-a888-f535b691d047

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames
public import Theorems.Thm_Light_frame_refreshLocals

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}
namespace Light
namespace LocalsBut
theorem _root_.solution (h : LocalsBut xs l loc) : loc = frame (refreshLocals l loc xs) := by
  funext y
  rw [frame_refreshLocals]
  split_ifs with hy
  · rfl
  · exact h y hy
end LocalsBut
end Light
