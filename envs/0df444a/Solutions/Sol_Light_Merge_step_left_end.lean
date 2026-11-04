-- Prove2me | solution 1 for Light.Merge.step_left_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:24.495919+00:00
-- url     : https://prove2.me/submissions/2dd969da-9212-4423-8459-44f934df4534

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tactics
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Merge

set_option autoImplicit false
section
open Light
variable {lim : Limits} {P : Program} {d : ℕ}
open Light.Merge
variable {l r : List ℤ} {i j : ℕ}
namespace Light.Merge
theorem _root_.solution (hi : i < l.length) (hj : r.length ≤ j) :
    (l.drop i).merge (r.drop j) = l[i] :: (l.drop (i + 1)).merge (r.drop j) := by
  rw [List.drop_eq_nil_of_le hj, List.merge_right, List.merge_right, List.drop_eq_getElem_cons hi]
end Light.Merge
