-- Prove2me | solution 1 for KhachiyanRound.BCD.lemma_1
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:32:57.005462+00:00
-- url     : https://prove2.me/submissions/4d29fd0f-4f97-4ae0-a7eb-c886a630ad87

import Mathlib
import Definitions.Def_LinearOptimization_Ellipsoid
import Definitions.Def_KhachiyanRound_BCD_Setting
set_option autoImplicit false
open KhachiyanRound.BCD

theorem solution {ι : Type*} [Fintype ι] {n : ℕ} (a : ι → Fin n → ℝ)
    (p : ι → ℝ) (hp : p ∈ SF a) :
    ∑ j, p j * w a p j = (n : ℝ) := by
  have hdet : 0 < (momentMatrix a p).det := hp.2
  have hM : IsUnit (momentMatrix a p).det := isUnit_iff_ne_zero.2 hdet.ne'
  have h1 : (momentMatrix a p)⁻¹ * momentMatrix a p = 1 := Matrix.nonsing_inv_mul _ hM
  have h2 := congrArg Matrix.trace h1
  rw [Matrix.trace_one, Fintype.card_fin] at h2
  rw [← h2]
  set N := (momentMatrix a p)⁻¹ with hN
  have h3 : Matrix.trace (N * momentMatrix a p)
      = ∑ k, ∑ l, N k l * ∑ j, p j * (a j l * a j k) := by
    simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, momentMatrix, Matrix.sum_apply,
      Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  rw [h3]
  unfold w
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  rw [← hN]
  calc _ = ∑ k, ∑ j, ∑ l, p j * (a j k * (N k l * a j l)) := by rw [Finset.sum_comm]
    _ = ∑ k, ∑ l, ∑ j, p j * (a j k * (N k l * a j l)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.sum_comm]
    _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        apply Finset.sum_congr rfl
        intro l _
        apply Finset.sum_congr rfl
        intro j _
        ring
