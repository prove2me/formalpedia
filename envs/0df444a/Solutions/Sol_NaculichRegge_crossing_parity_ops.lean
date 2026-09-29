-- Prove2me | solution 1 for NaculichRegge.crossing_parity_ops
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-28T21:39:11.185935+00:00
-- url     : https://prove2.me/submissions/0da68fe3-69b1-46c0-8903-c1f1fcf95d67

import Definitions.Def_NaculichRegge_TraceBasis

open Polynomial
open NaculichRegge

theorem solution :
    crossing * Tt2 * crossing = Tt2 ∧ crossing * Tsu2 * crossing = -Tsu2 ∧
      crossing.mulVec C00 = -C00 := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crossing, Tt2, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [crossing, Tsu2, Matrix.mul_apply, Fin.sum_univ_succ]
  · ext i
    fin_cases i <;> simp [crossing, C00, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
