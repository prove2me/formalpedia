-- Prove2me | solution 1 for Matrix.pow_five_eq_one_of_trace_sq_add_trace_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/a1c4220d-59eb-5887-8147-c95c102c6c90

import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.LinearCombination
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one

open Polynomial

namespace Matrix
p2m_export "Matrix" "row aeval_self_charpoly charpoly charpoly_fin_two det of trace"
p2m_open "Matrix"

variable {R : Type*} [CommRing R]

theorem pow_five_aux (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1)
    (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 := by
  nontriviality R
  set t := g.trace with ht_def
  have e1 : (C t : R[X]) ^ 4 - 3 * C t ^ 2 + 1 = 0 := by
    have : t ^ 4 - 3 * t ^ 2 + 1 = 0 := by linear_combination (t ^ 2 - t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have e2 : (C t : R[X]) ^ 3 - 2 * C t + 1 = 0 := by
    have : t ^ 3 - 2 * t + 1 = 0 := by linear_combination (t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have key : (X ^ 5 - 1 : R[X]) =
      g.charpoly * (X ^ 3 + C t * X ^ 2 + (C t ^ 2 - 1) * X + (C t ^ 3 - 2 * C t)) := by
    rw [Matrix.charpoly_fin_two, hdet, map_one]
    linear_combination X * e1 - e2
  have h := Matrix.aeval_self_charpoly g
  have : aeval g (X ^ 5 - 1 : R[X]) = 0 := by rw [key, map_mul, h, zero_mul]
  simpa [sub_eq_zero] using this

end Matrix

theorem solution {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1) (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 :=
  Matrix.pow_five_aux g hdet ht

#print axioms solution

end S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one
end P2MW
export P2MW.S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one (solution)
