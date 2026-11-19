-- Prove2me | solution 1 for OAI.Saxl.Band.blocks_scaled
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-18T17:12:15.935593+00:00
-- url     : https://prove2.me/submissions/5ad9e484-6d9e-4cef-9810-acf5a7521b38

import Mathlib
import Definitions.Def_OAIQ259US001
import Theorems.Thm_OAI_Saxl_Band_segment_scaled

section
-- module Solutions.OAIQ259_US.Saxl_BandMatrices
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped TensorProduct

universe uA

namespace Saxl.Band

lemma scaledBasis_one : ScaledBasis 1 := by
  exact ⟨1, one_ne_zero, 0, by simp [basis]⟩

lemma basis_mul (i j : Fin 4) : ScaledBasis (basis i.val * basis j.val) := by
  fin_cases i <;> fin_cases j
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 3, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 2, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨1, by norm_num, 1, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])
  · refine ⟨-1, by norm_num, 0, ?_⟩
    ext a b
    fin_cases a <;> fin_cases b <;>
      (first | (simp [basis, Matrix.mul_apply, Fin.sum_univ_two]; all_goals first | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | rfl | decide) | (norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two]; done) | norm_num [basis, Matrix.mul_apply, Fin.sum_univ_two])

lemma ScaledBasis.mul {X Y : Mat} (hX : ScaledBasis X) (hY : ScaledBasis Y) :
    ScaledBasis (X * Y) := by
  obtain ⟨c, hc, i, rfl⟩ := hX
  obtain ⟨d, hd, j, rfl⟩ := hY
  obtain ⟨e, he, k, hk⟩ := basis_mul i j
  refine ⟨c * d * e, mul_ne_zero (mul_ne_zero hc hd) he, k, ?_⟩
  rw [smul_mul_smul_comm, hk, smul_smul]

lemma blocks_scaled_oai (rs : List ℕ) (hrs : ∀ r ∈ rs, 1 ≤ r ∧ r ≤ 4) (p : ℕ) :
    ScaledBasis (blocks p rs) := by
  induction rs generalizing p with
  | nil => exact scaledBasis_one
  | cons r rs ih =>
    exact (segment_scaled r p (hrs r (by simp))).mul
      (ih (fun a ha => hrs a (by simp [ha])) (p + r))

end Saxl.Band

end

end OAI
end

theorem solution : type_of% @OAI.Saxl.Band.blocks_scaled_oai := @OAI.Saxl.Band.blocks_scaled_oai
