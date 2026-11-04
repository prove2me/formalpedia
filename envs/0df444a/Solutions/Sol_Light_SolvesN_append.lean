-- Prove2me | solution 1 for Light.SolvesN.append
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:16.63264+00:00
-- url     : https://prove2.me/submissions/5c7a5487-8858-42e2-be20-fe1a2019e00e

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
namespace SolvesN
theorem _root_.solution {task : TaskN} {P : Program} {p : ℕ} {T : List ℕ → ℕ} {need : List ℕ → Need}
    (h : SolvesN task P p T need) (R : Program) : SolvesN task (P ++ R) p T need := by
  obtain ⟨body, hp, hb⟩ := h
  refine ⟨body, getElem?_append_of_eq_some hp R, fun R' lim d x μ fr hpre hok => ?_⟩
  rw [List.append_assoc]
  exact hb (R ++ R') lim d x μ fr hpre hok
end SolvesN
end Light
