-- Prove2me | solution 1 for Matrix.trace_pow_eq_of_trace_eq_of_det_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.007888+00:00
-- url     : https://prove2.me/submissions/81b3bab2-0130-5301-b7af-84e01a42d5c3

import Definitions.Def_TaylorWiles_Primes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq

theorem solution {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simpa using htr
    | (k + 2) =>
      rw [Matrix.trace_pow_add_two, Matrix.trace_pow_add_two, htr, hdet,
        ih (k + 1) (by omega), ih k (by omega)]

end S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq
end P2MW
export P2MW.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq (solution)
