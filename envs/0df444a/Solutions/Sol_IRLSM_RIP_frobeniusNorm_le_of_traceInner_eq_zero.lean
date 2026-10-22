-- Prove2me | solution 1 for IRLSM.RIP.frobeniusNorm_le_of_traceInner_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:48:54.489506+00:00
-- url     : https://prove2.me/submissions/ffa74524-2688-4c33-88be-a0d2cc43e504

import Mathlib
import Definitions.Def_IRLSM_Convergence_Basic

set_option autoImplicit false
open HighDimStat.MatrixRank Matrix

theorem solution {n p : ℕ} (H K : Matrix (Fin n) (Fin p) ℝ)
    (h : traceInner H K = 0) :
    frobeniusNorm H ≤ frobeniusNorm (H + K) := by
  unfold frobeniusNorm
  apply Real.sqrt_le_sqrt
  unfold traceInner at h
  have e : ∑ i, ∑ j, ((H + K) i j) ^ 2 =
      ∑ i, ∑ j, (H i j) ^ 2 + 2 * ∑ i, ∑ j, H i j * K i j + ∑ i, ∑ j, (K i j) ^ 2 := by
    simp only [Matrix.add_apply, add_sq, Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    · congr 1
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [e, h]
  have : 0 ≤ ∑ i, ∑ j, (K i j) ^ 2 := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith
