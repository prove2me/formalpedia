-- Prove2me | solution 1 for HighDimStat.RandomMatrices.thresholding_deterministic_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T03:14:54.567026+00:00
-- url     : https://prove2.me/submissions/f4f3b25c-02ce-4e1d-a78a-cd591137a321

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_maxNorm
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

namespace HighDimStat.RandomMatrices

theorem aux_tdb_norm_mono {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (h : ∀ i, |u i| ≤ |v i|) : ‖u‖ ≤ ‖v‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  apply Finset.sum_le_sum
  intro i _
  simp only [Real.norm_eq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2

theorem aux_tdb_entry {d : ℕ} (SigHat Sig : Matrix (Fin d) (Fin d) ℝ)
    (lam : ℝ) (hlam : 0 ≤ lam) (hent : ∀ i j, |SigHat i j - Sig i j| ≤ lam) (i j : Fin d) :
    |(thresholdMatrix lam SigHat - Sig) i j| ≤ 2 * lam * adjacencyMatrix Sig i j := by
  have h := hent i j
  simp only [thresholdMatrix, adjacencyMatrix, Matrix.sub_apply, Matrix.of_apply]
  by_cases hs : Sig i j = 0
  · have hn : ¬ lam < |SigHat i j| := by
      rw [hs, sub_zero] at h
      exact not_lt.mpr h
    simp [hs, hn]
  · simp only [ne_eq, hs, not_false_eq_true, if_true, mul_one]
    split_ifs with hk
    · linarith
    · have h1 : |Sig i j| ≤ |SigHat i j| + |SigHat i j - Sig i j| := by
        have := abs_sub_abs_le_abs_sub (Sig i j) (SigHat i j)
        rw [abs_sub_comm (Sig i j)] at this
        linarith
      rw [zero_sub, abs_neg]
      rw [not_lt] at hk
      linarith

end HighDimStat.RandomMatrices

open HighDimStat.RandomMatrices

theorem solution {d : ℕ} (SigHat Sig : Matrix (Fin d) (Fin d) ℝ)
    (lam : ℝ) (hmax : maxNorm (SigHat - Sig) ≤ lam) :
    opNorm (thresholdMatrix lam SigHat - Sig) ≤ 2 * opNorm (adjacencyMatrix Sig) * lam := by
  have hent : ∀ i j, |SigHat i j - Sig i j| ≤ lam := fun i j => by
    have : |(SigHat - Sig) i j| ≤ maxNorm (SigHat - Sig) := by
      unfold maxNorm
      exact le_ciSup (f := fun p : Fin d × Fin d => |(SigHat - Sig) p.1 p.2|)
        (Set.finite_range _).bddAbove (i, j)
    simpa using this.trans hmax
  have hlam : 0 ≤ lam := le_trans (Real.iSup_nonneg (fun p => abs_nonneg _)) hmax
  have hE := aux_tdb_entry SigHat Sig lam hlam hent
  set E := thresholdMatrix lam SigHat - Sig with hEdef
  set A := adjacencyMatrix Sig with hAdef
  have hA0 : ∀ i j, 0 ≤ A i j := fun i j => by
    simp only [hAdef, adjacencyMatrix, Matrix.of_apply]
    split_ifs <;> norm_num
  unfold opNorm
  have hopA : 0 ≤ ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ := norm_nonneg _
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro x
  let y : EuclideanSpace ℝ (Fin d) := WithLp.toLp 2 (fun j => |x j|)
  have hy : ‖y‖ = ‖x‖ := by
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    simp [y]
  have key : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E x‖ ≤
      ‖(2 * lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A y‖ := by
    apply aux_tdb_norm_mono
    intro i
    have e1 : (Matrix.toEuclideanCLM (𝕜 := ℝ) E x) i = ∑ j, E i j * x j := rfl
    have e2 : ((2 * lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A y) i
        = 2 * lam * ∑ j, A i j * |x j| := rfl
    rw [e1, e2]
    have hnn : 0 ≤ 2 * lam * ∑ j, A i j * |x j| := by
      apply mul_nonneg (by positivity)
      exact Finset.sum_nonneg (fun j _ => mul_nonneg (hA0 i j) (abs_nonneg _))
    rw [abs_of_nonneg hnn]
    calc |∑ j, E i j * x j| ≤ ∑ j, |E i j * x j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, |E i j| * |x j| := by simp [abs_mul]
      _ ≤ ∑ j, 2 * lam * A i j * |x j| := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hE i j) (abs_nonneg _)
      _ = 2 * lam * ∑ j, A i j * |x j| := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
  calc ‖Matrix.toEuclideanCLM (𝕜 := ℝ) E x‖
      ≤ ‖(2 * lam) • Matrix.toEuclideanCLM (𝕜 := ℝ) A y‖ := key
    _ = 2 * lam * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A y‖ := by
        rw [norm_smul, Real.norm_of_nonneg (by positivity)]
    _ ≤ 2 * lam * (‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * ‖y‖) := by
        gcongr
        exact ContinuousLinearMap.le_opNorm _ _
    _ = 2 * ‖Matrix.toEuclideanCLM (𝕜 := ℝ) A‖ * lam * ‖x‖ := by
        rw [hy]; ring
