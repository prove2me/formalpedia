-- Prove2me | solution 1 for OAI.PiExponent.finite_log_minor_mean_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-24T04:42:45.643581+00:00
-- url     : https://prove2.me/submissions/4a6f79f5-fa80-4c26-900e-4ca1479a6fc9

import Definitions.Def_PiExponent_FiniteMinorComparison
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_rowWeight_bounds
import Theorems.Thm_OAI_PiExponent_MatrixArithmetic_row_nonempty

open OAI.PiExponent
open Filter Topology
open scoped BigOperators

set_option maxHeartbeats 1000000 in
theorem solution
    (m K : ℕ) (v0 theta H : ℝ) (q : Fin m → ℕ)
    (hK : 0 < K) (hv0 : 0 < v0) (htheta : 0 < theta)
    (hH : 0 < H) (hq : ∀ i, 2 ≤ q i) :
    0 ≤ OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ∧
      OAI.PiExponent.MatrixArithmetic.meanRowWeight K v0 theta q H ≤ theta := by
  classical
  let R := OAI.PiExponent.InterpolationMatrix.Row K v0 theta
    (OAI.PiExponent.MatrixArithmetic.logWeights q) H
  let N : ℝ := ∑ ρ : R, ∑ i : Fin m,
    (ρ.2.1 i.succ : ℝ) * OAI.PiExponent.MatrixArithmetic.logWeights q i
  have hR : 0 < Fintype.card R :=
    OAI.PiExponent.MatrixArithmetic.row_nonempty m K v0 theta H q
      hK hv0 htheta hH hq
  have hN0 : 0 ≤ N := by
    dsimp [N]
    exact Finset.sum_nonneg fun ρ _ =>
      (OAI.PiExponent.MatrixArithmetic.rowWeight_bounds m K v0 theta H q
        hK hv0 htheta hH hq ρ).1
  have hNle : N ≤ (Fintype.card R : ℝ) * (theta * H) := by
    dsimp [N]
    calc
      (∑ ρ : R, ∑ i : Fin m,
          (ρ.2.1 i.succ : ℝ) * OAI.PiExponent.MatrixArithmetic.logWeights q i)
          ≤ ∑ ρ : R, theta * H :=
        Finset.sum_le_sum fun ρ _ =>
          (OAI.PiExponent.MatrixArithmetic.rowWeight_bounds m K v0 theta H q
            hK hv0 htheta hH hq ρ).2
      _ = (Fintype.card R : ℝ) * (theta * H) := by simp
  have hcard : (Fintype.card R : ℝ) > 0 := by exact_mod_cast hR
  have hD : 0 < (Fintype.card R : ℝ) * H := mul_pos hcard hH
  have hNupper : N ≤ theta * ((Fintype.card R : ℝ) * H) := by
    calc
      N ≤ (Fintype.card R : ℝ) * (theta * H) := hNle
      _ = theta * ((Fintype.card R : ℝ) * H) := by ring
  constructor
  · change 0 ≤ N / ((Fintype.card R : ℝ) * H)
    exact div_nonneg hN0 (le_of_lt hD)
  · change N / ((Fintype.card R : ℝ) * H) ≤ theta
    rw [div_le_iff₀ hD]
    exact hNupper