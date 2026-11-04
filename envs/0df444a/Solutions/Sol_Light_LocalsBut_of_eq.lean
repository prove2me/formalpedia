-- Prove2me | solution 1 for Light.LocalsBut.of_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:50.561066+00:00
-- url     : https://prove2.me/submissions/440c5903-71c4-4b0b-9d08-3d03a5116698

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
theorem _root_.solution (h : SameFrame (refreshLocals l (frame l') xs) l') :
    LocalsBut xs l (frame l') := by
  intro y hy
  have hread := frame_refreshLocals (frame l') y xs l
  rw [h, if_neg hy] at hread
  exact hread
end LocalsBut
end Light
