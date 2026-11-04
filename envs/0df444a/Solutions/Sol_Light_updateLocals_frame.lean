-- Prove2me | solution 1 for Light.updateLocals_frame
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:31:42.072021+00:00
-- url     : https://prove2.me/submissions/c55ea921-9171-4278-9cdf-529e496d7e55

module
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Assigns
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
public import Definitions.Def_Submission_ThreeSumApsp_Lang_Frames

set_option autoImplicit false
public section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
namespace Light
theorem _root_.solution : ∀ (ps : List (ℕ × ℤ)) (l : List ℤ),
    updateLocals (frame l) ps = frame (setLocals l ps)
  | [], _ => rfl
  | p :: ps, l => by
    rw [updateLocals, update_frame_setLocal, solution ps, setLocals]
end Light
