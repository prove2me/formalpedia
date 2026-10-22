-- Prove2me | solution 1 for NAGFlow.GSSpectrum.eq_124
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:24:32.83941+00:00
-- url     : https://prove2.me/submissions/eccd78ce-9f83-48de-b4a4-65350e71b6ca

import Mathlib
import Definitions.Def_NAGFlow_GSSpectrum_Setting

set_option autoImplicit false
open Matrix NAGFlow.GSSpectrum

theorem solution (a b c d α : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (htr : (Rmat a b c d).trace < 0) (hdet : 0 < (Rmat a b c d).det) (hα : 0 < α) :
    ER α (Rmat a b c d) = (1 / ((1 + a * α) * (1 + d * α))) •
        !![1 + d * α, c * α * (1 + d * α); -(b * α), 1 + a * α - b * c * α ^ 2] ∧
      0 < (ER α (Rmat a b c d)).det ∧
      (ER α (Rmat a b c d)).det = 1 / ((1 + a * α) * (1 + d * α)) ∧
      1 / ((1 + a * α) * (1 + d * α)) = 1 / (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2) ∧
      1 / (1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2) < 1 := by
  have h1 : 0 < 1 + a * α := by positivity
  have h2 : 0 < 1 + d * α := by positivity
  have hδ : (1 + a * α) * (1 + d * α) ≠ 0 := by positivity
  have htr' : (Rmat a b c d).trace = -(a + d) := by
    simp [Rmat, Matrix.trace, Fin.sum_univ_two]; ring
  have hsum : 0 < a + d := by rw [htr'] at htr; linarith
  have hmain : ER α (Rmat a b c d) = (1 / ((1 + a * α) * (1 + d * α))) •
        !![1 + d * α, c * α * (1 + d * α); -(b * α), 1 + a * α - b * c * α ^ 2] := by
    have hinv : (1 - α • lowerTri2 (Rmat a b c d))⁻¹ =
        (1 / ((1 + a * α) * (1 + d * α))) • !![1 + d * α, 0; -(b * α), 1 + a * α] := by
      apply Matrix.inv_eq_right_inv
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [lowerTri2, Rmat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
    unfold ER gsE
    rw [hinv]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [lowerTri2, Rmat, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring
  have hdetE : (ER α (Rmat a b c d)).det = 1 / ((1 + a * α) * (1 + d * α)) := by
    rw [hmain, Matrix.det_smul]
    simp [Matrix.det_fin_two]
    field_simp
    ring
  have habs : |(Rmat a b c d).trace| = a + d := by
    rw [htr', abs_neg, abs_of_pos hsum]
  have hq : (1 + a * α) * (1 + d * α) = 1 + |(Rmat a b c d).trace| * α + a * d * α ^ 2 := by
    rw [habs]; ring
  refine ⟨hmain, ?_, hdetE, ?_, ?_⟩
  · rw [hdetE]; positivity
  · rw [hq]
  · rw [← hq, div_lt_one (by positivity)]
    nlinarith [mul_pos hα hsum, mul_nonneg ha hd, mul_nonneg (mul_nonneg ha hd) (mul_nonneg hα.le hα.le)]
