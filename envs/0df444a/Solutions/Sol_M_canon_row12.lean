-- Prove2me | solution 1 for M_canon_row12
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T08:46:30.85909+00:00
-- url     : https://prove2.me/submissions/7c38c906-1ff6-46bc-b045-6461cd7f3a54

import Mathlib
import Definitions.Def_LisonekSaltConic

set_option autoImplicit true
open Matrix
variable (p : ℕ) [Fact p.Prime]
theorem _root_.solution (n x : ZMod p) (h2 : (2 : ZMod p) ≠ 0) :
    (M_canon p n).mulVec (row12_orig p x) = ![x^2, x, 0, 0] := by
  ext i
  fin_cases i <;> simp [M_canon, row12_orig, mulVec, dotProduct, Fin.sum_univ_four] <;>
    field_simp <;> ring
