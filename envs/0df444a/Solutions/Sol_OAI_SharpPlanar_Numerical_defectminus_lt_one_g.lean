-- Prove2me | solution 1 for OAI.SharpPlanar.Numerical.defectminus_lt_one_g
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-08T09:09:55.471765+00:00
-- url     : https://prove2.me/submissions/8b33e0de-f4c2-4702-a8b8-4476d293bcc7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ098G004
import Theorems.Thm_OAI_SharpPlanar_Numerical_defectminus_column_g
import Theorems.Thm_OAI_SharpPlanar_l1Finite_norm_g

section
-- module Solutions.OAIQ098_PP.PlanarPacking_MatrixL1
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace SharpPlanar
open scoped BigOperators

section
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq ι] in
lemma matrixL1_apply (A : Matrix ι κ ℝ) (x : L1Finite κ) (i : ι) :
    matrixL1 A x i = ∑ j, A i j*x j := rfl

omit [DecidableEq ι] in
lemma matrixL1_mul (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) :
    matrixL1 (A*B) = (matrixL1 A).comp (matrixL1 B) := by
  apply ContinuousLinearMap.ext
  intro x
  change Matrix.toLpLin 1 1 (A*B) x = Matrix.toLpLin 1 1 A (Matrix.toLpLin 1 1 B x)
  rw [Matrix.toLpLin_mul (q:=1)]
  rfl
omit [DecidableEq ι] in
lemma matrixL1_sub (A B : Matrix ι κ ℝ) :
    matrixL1 (A-B) = matrixL1 A-matrixL1 B := by
  ext x i
  simp [matrixL1_apply,sub_mul,Finset.sum_sub_distrib]
lemma matrixL1_one : matrixL1 (1:Matrix ι ι ℝ) = 1 := by
  ext x i
  simp [matrixL1_apply,Matrix.one_apply]

omit [DecidableEq ι] in
lemma matrixL1_norm_le {A : Matrix ι κ ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hA : ∀ j, ∑ i, |A i j| ≤ b) : ‖matrixL1 A‖ ≤ b := by
  apply ContinuousLinearMap.opNorm_le_bound _ hb
  intro x
  rw [l1Finite_norm_g,l1Finite_norm_g,Finset.mul_sum]
  calc
    ∑ i, |matrixL1 A x i| ≤ ∑ i, ∑ j, |A i j| * |x j| := by
      apply Finset.sum_le_sum
      intro i _
      rw [matrixL1_apply]
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun j => A i j*x j) Finset.univ
    _ = ∑ j, (∑ i, |A i j|)* |x j| := by rw [Finset.sum_comm]; simp_rw [Finset.sum_mul]
    _ ≤ ∑ j, b* |x j| := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hA j) (abs_nonneg _)

omit [DecidableEq ι] in
lemma matrixL1_norm_lt [Nonempty κ] {A : Matrix ι κ ℝ} {b : ℝ}
    (hA : ∀ j, ∑ i, |A i j| < b) : ‖matrixL1 A‖ < b := by
  obtain ⟨j,_,hj⟩ := Finset.exists_max_image Finset.univ (fun j : κ => ∑ i, |A i j|) Finset.univ_nonempty
  exact (matrixL1_norm_le (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    (fun k => hj k (Finset.mem_univ _))).trans_lt (hA j)
end

end SharpPlanar

end OAI
end

section
-- module Solutions.OAIQ098_PP.PlanarPacking_FiniteInverse
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-!
# Inverse bounds for the central interpolation block

Exact rational approximate inverses give bounds for the two central blocks.
-/

namespace SharpPlanar.Numerical
lemma defectminus_norm : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < (1:ℝ)/1000 := by
  have hh := matrixL1_norm_lt defectminus_column_g
  rw [matrixL1_sub,matrixL1_one,matrixL1_mul] at hh
  exact hh
lemma defectminus_lt_one_g_oai : ‖1-(matrixL1 Wminus)*(matrixL1 Aminus)‖ < 1 :=
  defectminus_norm.trans (by norm_num)
end SharpPlanar.Numerical

end OAI
end

theorem solution : type_of% @OAI.SharpPlanar.Numerical.defectminus_lt_one_g_oai := @OAI.SharpPlanar.Numerical.defectminus_lt_one_g_oai
