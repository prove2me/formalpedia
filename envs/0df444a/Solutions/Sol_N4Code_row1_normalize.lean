-- Prove2me | solution 1 for N4Code.row1_normalize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:43.001274+00:00
-- url     : https://prove2.me/submissions/64a012ed-dbae-4672-990d-411534afbe42

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_permEven_j

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (i j : Fin 4) (hij : i ≠ j) :
    row (normalizeCode C i j) 1 = bitXor (row C i) (row C j) := by
  funext t
  have hj : (permEven i j).symm (1 : Fin 4) = j :=
    (Equiv.symm_apply_eq (e := permEven i j) (x := (1 : Fin 4)) (y := j)).mpr
      (permEven_j i j hij).symm
  unfold row colBit normalizeCode rowPermute
  rw [hj]
  by_cases hc : C t i
  · simp [row, colBit, flipCol, hc, bitXor]
  · simp [row, colBit, hc, bitXor]
end N4Code
