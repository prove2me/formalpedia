-- Prove2me | solution 1 for Light.Solves.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:15.571669+00:00
-- url     : https://prove2.me/submissions/8b4ce81d-4c06-488f-a830-cda518530a95

import Definitions.Def_Submission_ThreeSumApsp_Lang_Calls
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_WordSize
import Definitions.Def_Submission_ThreeSumApsp_Lang_Tasks
import Theorems.Thm_P2M_Light_getElem__append_of_eq_some_9fa037aa12b5


set_option autoImplicit false
section
open Light
open ThreeSumApsp
namespace Light
namespace Solves
theorem _root_.solution {task : Task} {P : Program} {p : ℕ} {T : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P p T need) (R : Program) : Solves task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R, fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok
end Solves
end Light
