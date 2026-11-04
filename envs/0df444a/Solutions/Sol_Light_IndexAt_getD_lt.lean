-- Prove2me | solution 1 for Light.IndexAt.getD_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:56:55.891487+00:00
-- url     : https://prove2.me/submissions/a765578d-2b20-4e6a-88f4-9c172a3f601d

import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_Seg
import Definitions.Def_Submission_ThreeSumApsp_Lang_Rules
import Definitions.Def_Submission_ThreeSumApsp_Lang_Lib_ArrayAt

set_option autoImplicit false
section
open Light
open ThreeSumApsp
variable {μ μ' : ℕ → ℤ} {a N top top' i k n : ℕ} {l : List ℤ} {U U' : ℤ}
open Light.IndexAt
variable {l : List ℕ} {p : ℕ}
namespace Light.IndexAt
theorem _root_.solution (h : IndexAt μ a l N p top) (hi : i < N) : l.getD i 0 < p := by
  have hl : i < l.length := h.len ▸ hi
  rw [List.getD_eq_getElem _ 0 hl]
  exact h.lt _ (List.getElem_mem hl)
end Light.IndexAt
