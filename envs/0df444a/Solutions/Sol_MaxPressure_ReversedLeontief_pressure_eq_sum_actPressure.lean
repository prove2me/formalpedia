-- Prove2me | solution 1 for MaxPressure.ReversedLeontief.pressure_eq_sum_actPressure
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T15:49:07.852674+00:00
-- url     : https://prove2.me/submissions/960a1038-911f-478c-8656-fdb396bc30b1

import Mathlib
import Definitions.Def_MaxPressure_ReversedLeontief_Network

open MaxPressure.ReversedLeontief in
theorem solution {I J K : ℕ} (N : Network I J K)
    (a : Fin J → ℝ) (z : Fin I → ℝ) :
    pressure N a z = ∑ j, a j * actPressure N j z := by
  simp only [pressure, actPressure, dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring
