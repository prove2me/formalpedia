-- Prove2me | solution 1 for M_canon_det
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:49:19.358662+00:00
-- url     : https://prove2.me/submissions/78a228d8-4c8d-4c9e-913f-7f9101952f72

import Mathlib
import Definitions.Def_LisonekSaltConic

set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]
theorem _root_.solution (n : ZMod p) : (M_canon p n).det = -2 := by
  simp [M_canon, det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  ring
