-- Prove2me | solution 1 for Light.sameFrame_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:32:11.555108+00:00
-- url     : https://prove2.me/submissions/4097bec7-2d77-4a17-874e-cb4536ac604b

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution : SameFrame [] [] := rfl
end Light
