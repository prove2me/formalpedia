-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_10_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:31:14.328096+00:00
-- url     : https://prove2.me/submissions/bdce25ec-46a2-4b32-aeb9-561851121976

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L005

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_MatrixCompute
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate.MatrixCompute

open scoped BigOperators

theorem middle_apply (D : ℕ) (Y : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    middle D Y i j =
      (if i = j then ((if copyLabel i = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D i else 0) -
        copyWeight D i * Y i j * copyWeight D j := by
  simp only [middle, Matrix.sub_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
    Matrix.diagonal_apply]

theorem compressed_apply (D : ℕ) (Y Z : Matrix (Fin ((D+1)/2)) (Fin ((D+1)/2)) ℚ)
    (i j : Fin ((D+1)/2)) :
    compressed D Y Z i j =
      ∑ k, (∑ l, Z i l *
        ((if l = k then ((if copyLabel l = 1 then 2 else 0) + (3/10^6 : ℚ)) * copyWeight D l else 0) -
          copyWeight D l * Y l k * copyWeight D k)) * Z k j := by
  simp only [compressed, Matrix.mul_apply, middle_apply]

theorem ldl_apply {n : ℕ} (L : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ)
    (i j : Fin n) :
    (L * Matrix.diagonal d * L.transpose) i j = ∑ k, L i k * d k * L j k := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply]

end Laughlin.Certificate.MatrixCompute

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_10_0_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_3 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 3 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_1_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_1_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_1_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_1_3 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 3 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_1_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_2_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_2_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_2_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_2_3 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 3 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_2_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_3_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_3_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_3_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_3_3 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 3 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_3_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_3 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 3 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_10_s50_oai : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 =
    lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_10_0_0
  · exact computeLDL_10_0_1
  · exact computeLDL_10_0_2
  · exact computeLDL_10_0_3
  · exact computeLDL_10_0_4
  · exact computeLDL_10_1_0
  · exact computeLDL_10_1_1
  · exact computeLDL_10_1_2
  · exact computeLDL_10_1_3
  · exact computeLDL_10_1_4
  · exact computeLDL_10_2_0
  · exact computeLDL_10_2_1
  · exact computeLDL_10_2_2
  · exact computeLDL_10_2_3
  · exact computeLDL_10_2_4
  · exact computeLDL_10_3_0
  · exact computeLDL_10_3_1
  · exact computeLDL_10_3_2
  · exact computeLDL_10_3_3
  · exact computeLDL_10_3_4
  · exact computeLDL_10_4_0
  · exact computeLDL_10_4_1
  · exact computeLDL_10_4_2
  · exact computeLDL_10_4_3
  · exact computeLDL_10_4_4

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_10_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_10_s50_oai
