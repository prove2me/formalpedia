-- Prove2me | solution 1 for LogBarrierIPM.Iterations.proposition_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T02:07:28.956468+00:00
-- url     : https://prove2.me/submissions/d344d51b-0d41-45f6-ad98-0f2d2533ff55

import Mathlib
import Definitions.Def_LogBarrierIPM_Iterations_SlackLP

open Matrix in
open LogBarrierIPM.Iterations in
theorem LogBarrierIPM_Iterations_prop1_key {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : Fin m → ℝ) (c : Fin n → ℝ) (z z' : PDPoint n m)
    (hz : z ∈ primalDualFeasible A b c) (hz' : z' ∈ primalDualFeasible A b c) :
    (z'.1 - z.1) ⬝ᵥ (z'.2.2.1 - z.2.2.1) + (z'.2.1 - z.2.1) ⬝ᵥ (z'.2.2.2 - z.2.2.2) = 0 := by
  obtain ⟨h1, h2, -⟩ := hz
  obtain ⟨h1', h2', -⟩ := hz'
  have hs : z'.2.2.1 - z.2.2.1 = Aᵀ *ᵥ (z'.2.2.2 - z.2.2.2) := by
    rw [Matrix.mulVec_sub]
    have e1 : z'.2.2.1 = c + Aᵀ *ᵥ z'.2.2.2 := by rw [← h2']; abel
    have e2 : z.2.2.1 = c + Aᵀ *ᵥ z.2.2.2 := by rw [← h2]; abel
    rw [e1, e2]; abel
  have hw : z'.2.1 - z.2.1 = -(A *ᵥ (z'.1 - z.1)) := by
    rw [Matrix.mulVec_sub]
    have e1 : z'.2.1 = b - A *ᵥ z'.1 := by rw [← h1']; abel
    have e2 : z.2.1 = b - A *ᵥ z.1 := by rw [← h1]; abel
    rw [e1, e2]; abel
  rw [hs, hw, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, neg_dotProduct]
  ring

open LogBarrierIPM.Iterations in
theorem solution {n m : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (c : Fin n → ℝ) (z z' : PDPoint n m) (hz : z ∈ primalDualFeasible A b c)
    (hz' : z' ∈ primalDualFeasible A b c) (α : ℝ) :
    dualityMeasure ((1 - α) • z + α • z') =
      (1 - α) * dualityMeasure z + α * dualityMeasure z' := by
  have key := LogBarrierIPM_Iterations_prop1_key A b c z z' hz hz'
  have hnum : ((1 - α) • z + α • z').1 ⬝ᵥ ((1 - α) • z + α • z').2.2.1 +
      ((1 - α) • z + α • z').2.1 ⬝ᵥ ((1 - α) • z + α • z').2.2.2 =
      (1 - α) * (z.1 ⬝ᵥ z.2.2.1 + z.2.1 ⬝ᵥ z.2.2.2) +
        α * (z'.1 ⬝ᵥ z'.2.2.1 + z'.2.1 ⬝ᵥ z'.2.2.2) := by
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, dotProduct_add,
      add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at *
    simp only [dotProduct_sub, sub_dotProduct] at key
    linear_combination (-(α * (1 - α))) * key
  unfold dualityMeasure
  rw [hnum]
  ring
