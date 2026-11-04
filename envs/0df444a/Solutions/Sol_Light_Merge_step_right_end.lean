-- Prove2me | solution 1 for Light.Merge.step_right_end
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T10:27:25.658426+00:00
-- url     : https://prove2.me/submissions/0154171e-1cff-4756-8b0f-f1d27a0f6997

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
theorem _root_.solution (hi : l.length ≤ i) (hj : j < r.length) :
    (l.drop i).merge (r.drop j) = r[j] :: (l.drop i).merge (r.drop (j + 1)) := by
  rw [List.drop_eq_nil_of_le hi, List.nil_merge, List.nil_merge, List.drop_eq_getElem_cons hj]
end Light.Merge
