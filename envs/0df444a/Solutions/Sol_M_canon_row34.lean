-- Prove2me | solution 1 for M_canon_row34
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:48:05.46494+00:00
-- url     : https://prove2.me/submissions/41eeacc3-a4c9-47cc-bce6-3290861b6fa0

import Mathlib
import Definitions.Def_LisonekSaltConic

set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]
theorem _root_.solution (n y : ZMod p) (h2 : (2 : ZMod p) ≠ 0) (hn : n ≠ 0) :
    (M_canon p n).mulVec (row34_orig p n y) = ![y^2 * n⁻¹, 0, 1, y] := by
  ext i
  fin_cases i <;> simp [M_canon, row34_orig, mulVec, dotProduct, Fin.sum_univ_four] <;>
    field_simp <;> ring
