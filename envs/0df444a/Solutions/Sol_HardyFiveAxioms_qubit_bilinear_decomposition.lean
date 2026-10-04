-- Prove2me | solution 1 for HardyFiveAxioms.qubit_bilinear_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T09:47:14.976234+00:00
-- url     : https://prove2.me/submissions/30b18127-3a6a-4649-9451-f176c7a49c16

import Mathlib
import Definitions.Def_hardy2001_qubit

open HardyFiveAxioms Matrix in
theorem solution (a b c : ℝ) (v w : Fin 4 → ℝ) :
    (qubitC *ᵥ v) ⬝ᵥ (qubitD a b c *ᵥ (qubitC *ᵥ w)) =
      ![v 1, v 2, v 3] ⬝ᵥ (qubitA a b c *ᵥ ![w 1, w 2, w 3]) +
        (2 * v 0 + v 1 + v 2 + v 3) * (2 * w 0 + w 1 + w 2 + w 3) / 2 := by
  simp only [qubitC, qubitD, qubitA, mulVec, dotProduct, Fin.sum_univ_four, Fin.sum_univ_three,
    Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_cons, Matrix.head_fin_const, Matrix.tail_cons]
  ring
