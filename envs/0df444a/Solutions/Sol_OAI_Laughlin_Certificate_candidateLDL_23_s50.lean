-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_23_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:39:34.991978+00:00
-- url     : https://prove2.me/submissions/bb98a151-af56-4018-9f98-14bddb5c9f19

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_0_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_0_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_10_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_11_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_1_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_1_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_2_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_4_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_6_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_8_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_11_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_23_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_0_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_0_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 0 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_1_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_3 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 3 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_4 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 4 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_5 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 5 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_6 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 6 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_7 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 7 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_8 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 8 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_1_9 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 1 9 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 1 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL02Batch23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_23_2_0 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 0 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_1 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 1 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_23_2_2 : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 2 2 =
    (lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_23_s50_oai : MatrixCompute.compressed 23 candidateY_23 candidateZ_23 =
    lower_23 * Matrix.diagonal pivots_23 * lower_23.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_23_0_0
  · exact computeLDL_23_0_1
  · exact computeLDL_23_0_2
  · exact computeLDL_23_0_3
  · exact computeLDL_23_0_4
  · exact computeLDL_23_0_5
  · exact computeLDL_23_0_6
  · exact computeLDL_23_0_7
  · exact computeLDL_23_0_8
  · exact computeLDL_23_0_9
  · exact computeLDL_23_0_10_s50
  · exact computeLDL_23_0_11_s50
  · exact computeLDL_23_1_0
  · exact computeLDL_23_1_1
  · exact computeLDL_23_1_2
  · exact computeLDL_23_1_3
  · exact computeLDL_23_1_4
  · exact computeLDL_23_1_5
  · exact computeLDL_23_1_6
  · exact computeLDL_23_1_7
  · exact computeLDL_23_1_8
  · exact computeLDL_23_1_9
  · exact computeLDL_23_1_10_s50
  · exact computeLDL_23_1_11_s50
  · exact computeLDL_23_2_0
  · exact computeLDL_23_2_1
  · exact computeLDL_23_2_2
  · exact computeLDL_23_2_3_s50
  · exact computeLDL_23_2_4_s50
  · exact computeLDL_23_2_5_s50
  · exact computeLDL_23_2_6_s50
  · exact computeLDL_23_2_7_s50
  · exact computeLDL_23_2_8_s50
  · exact computeLDL_23_2_9_s50
  · exact computeLDL_23_2_10_s50
  · exact computeLDL_23_2_11_s50
  · exact computeLDL_23_3_0_s50
  · exact computeLDL_23_3_1_s50
  · exact computeLDL_23_3_2_s50
  · exact computeLDL_23_3_3_s50
  · exact computeLDL_23_3_4_s50
  · exact computeLDL_23_3_5_s50
  · exact computeLDL_23_3_6_s50
  · exact computeLDL_23_3_7_s50
  · exact computeLDL_23_3_8_s50
  · exact computeLDL_23_3_9_s50
  · exact computeLDL_23_3_10_s50
  · exact computeLDL_23_3_11_s50
  · exact computeLDL_23_4_0_s50
  · exact computeLDL_23_4_1_s50
  · exact computeLDL_23_4_2_s50
  · exact computeLDL_23_4_3_s50
  · exact computeLDL_23_4_4_s50
  · exact computeLDL_23_4_5_s50
  · exact computeLDL_23_4_6_s50
  · exact computeLDL_23_4_7_s50
  · exact computeLDL_23_4_8_s50
  · exact computeLDL_23_4_9_s50
  · exact computeLDL_23_4_10_s50
  · exact computeLDL_23_4_11_s50
  · exact computeLDL_23_5_0_s50
  · exact computeLDL_23_5_1_s50
  · exact computeLDL_23_5_2_s50
  · exact computeLDL_23_5_3_s50
  · exact computeLDL_23_5_4_s50
  · exact computeLDL_23_5_5_s50
  · exact computeLDL_23_5_6_s50
  · exact computeLDL_23_5_7_s50
  · exact computeLDL_23_5_8_s50
  · exact computeLDL_23_5_9_s50
  · exact computeLDL_23_5_10_s50
  · exact computeLDL_23_5_11_s50
  · exact computeLDL_23_6_0_s50
  · exact computeLDL_23_6_1_s50
  · exact computeLDL_23_6_2_s50
  · exact computeLDL_23_6_3_s50
  · exact computeLDL_23_6_4_s50
  · exact computeLDL_23_6_5_s50
  · exact computeLDL_23_6_6_s50
  · exact computeLDL_23_6_7_s50
  · exact computeLDL_23_6_8_s50
  · exact computeLDL_23_6_9_s50
  · exact computeLDL_23_6_10_s50
  · exact computeLDL_23_6_11_s50
  · exact computeLDL_23_7_0_s50
  · exact computeLDL_23_7_1_s50
  · exact computeLDL_23_7_2_s50
  · exact computeLDL_23_7_3_s50
  · exact computeLDL_23_7_4_s50
  · exact computeLDL_23_7_5_s50
  · exact computeLDL_23_7_6_s50
  · exact computeLDL_23_7_7_s50
  · exact computeLDL_23_7_8_s50
  · exact computeLDL_23_7_9_s50
  · exact computeLDL_23_7_10_s50
  · exact computeLDL_23_7_11_s50
  · exact computeLDL_23_8_0_s50
  · exact computeLDL_23_8_1_s50
  · exact computeLDL_23_8_2_s50
  · exact computeLDL_23_8_3_s50
  · exact computeLDL_23_8_4_s50
  · exact computeLDL_23_8_5_s50
  · exact computeLDL_23_8_6_s50
  · exact computeLDL_23_8_7_s50
  · exact computeLDL_23_8_8_s50
  · exact computeLDL_23_8_9_s50
  · exact computeLDL_23_8_10_s50
  · exact computeLDL_23_8_11_s50
  · exact computeLDL_23_9_0_s50
  · exact computeLDL_23_9_1_s50
  · exact computeLDL_23_9_2_s50
  · exact computeLDL_23_9_3_s50
  · exact computeLDL_23_9_4_s50
  · exact computeLDL_23_9_5_s50
  · exact computeLDL_23_9_6_s50
  · exact computeLDL_23_9_7_s50
  · exact computeLDL_23_9_8_s50
  · exact computeLDL_23_9_9_s50
  · exact computeLDL_23_9_10_s50
  · exact computeLDL_23_9_11_s50
  · exact computeLDL_23_10_0_s50
  · exact computeLDL_23_10_1_s50
  · exact computeLDL_23_10_2_s50
  · exact computeLDL_23_10_3_s50
  · exact computeLDL_23_10_4_s50
  · exact computeLDL_23_10_5_s50
  · exact computeLDL_23_10_6_s50
  · exact computeLDL_23_10_7_s50
  · exact computeLDL_23_10_8_s50
  · exact computeLDL_23_10_9_s50
  · exact computeLDL_23_10_10_s50
  · exact computeLDL_23_10_11_s50
  · exact computeLDL_23_11_0_s50
  · exact computeLDL_23_11_1_s50
  · exact computeLDL_23_11_2_s50
  · exact computeLDL_23_11_3_s50
  · exact computeLDL_23_11_4_s50
  · exact computeLDL_23_11_5_s50
  · exact computeLDL_23_11_6_s50
  · exact computeLDL_23_11_7_s50
  · exact computeLDL_23_11_8_s50
  · exact computeLDL_23_11_9_s50
  · exact computeLDL_23_11_10_s50
  · exact computeLDL_23_11_11_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_23_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_23_s50_oai
