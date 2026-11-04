-- Prove2me | solution 1 for Light.Solves.meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T08:11:11.329794+00:00
-- url     : https://prove2.me/submissions/cb558287-db1b-4f25-a7eb-7d4f036274bb

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
theorem _root_.solution {task : Task} {P₀ : Program} {p : ℕ} {T₀ : ℕ → ℕ → ℕ} {need : ℕ → ℕ → Need}
    (h : Solves task P₀ p T₀ need) (R : Program) {lim : Limits} {d : ℕ} (x : task.Inst) {μ : ℕ → ℤ}
    (fr : ℕ) (hpre : task.Pre x μ fr) (hok : (need (task.size x) (task.bound x)).Ok lim fr d) :
    Meets lim (P₀ ++ R) p d (task.args x ++ [(fr : ℤ)]) μ (T₀ (task.size x) (task.bound x))
      (task.Post x μ fr) := by
  obtain ⟨body, hp, hb⟩ := h
  exact ⟨body, getElem?_append_of_eq_some hp R, hb R lim d x μ fr hpre hok⟩
end Solves
end Light
