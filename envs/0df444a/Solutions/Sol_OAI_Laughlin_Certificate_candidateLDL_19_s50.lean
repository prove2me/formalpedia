-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_19_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:36:32.051198+00:00
-- url     : https://prove2.me/submissions/8e394957-d3a6-45d0-8b31-1a6ecb18baac

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_1_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_2_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_4_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_6_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_8_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_19_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_0_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_0_9 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 0 9 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_19_1_0 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 0 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_1 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 1 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_2 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 2 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_3 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 3 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_4 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 4 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_5 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 5 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_6 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 6 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_7 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 7 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_19_1_8 : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 1 8 =
    (lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData19
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_19_s50_oai : MatrixCompute.compressed 19 candidateY_19 candidateZ_19 =
    lower_19 * Matrix.diagonal pivots_19 * lower_19.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_19_0_0
  · exact computeLDL_19_0_1
  · exact computeLDL_19_0_2
  · exact computeLDL_19_0_3
  · exact computeLDL_19_0_4
  · exact computeLDL_19_0_5
  · exact computeLDL_19_0_6
  · exact computeLDL_19_0_7
  · exact computeLDL_19_0_8
  · exact computeLDL_19_0_9
  · exact computeLDL_19_1_0
  · exact computeLDL_19_1_1
  · exact computeLDL_19_1_2
  · exact computeLDL_19_1_3
  · exact computeLDL_19_1_4
  · exact computeLDL_19_1_5
  · exact computeLDL_19_1_6
  · exact computeLDL_19_1_7
  · exact computeLDL_19_1_8
  · exact computeLDL_19_1_9_s50
  · exact computeLDL_19_2_0_s50
  · exact computeLDL_19_2_1_s50
  · exact computeLDL_19_2_2_s50
  · exact computeLDL_19_2_3_s50
  · exact computeLDL_19_2_4_s50
  · exact computeLDL_19_2_5_s50
  · exact computeLDL_19_2_6_s50
  · exact computeLDL_19_2_7_s50
  · exact computeLDL_19_2_8_s50
  · exact computeLDL_19_2_9_s50
  · exact computeLDL_19_3_0_s50
  · exact computeLDL_19_3_1_s50
  · exact computeLDL_19_3_2_s50
  · exact computeLDL_19_3_3_s50
  · exact computeLDL_19_3_4_s50
  · exact computeLDL_19_3_5_s50
  · exact computeLDL_19_3_6_s50
  · exact computeLDL_19_3_7_s50
  · exact computeLDL_19_3_8_s50
  · exact computeLDL_19_3_9_s50
  · exact computeLDL_19_4_0_s50
  · exact computeLDL_19_4_1_s50
  · exact computeLDL_19_4_2_s50
  · exact computeLDL_19_4_3_s50
  · exact computeLDL_19_4_4_s50
  · exact computeLDL_19_4_5_s50
  · exact computeLDL_19_4_6_s50
  · exact computeLDL_19_4_7_s50
  · exact computeLDL_19_4_8_s50
  · exact computeLDL_19_4_9_s50
  · exact computeLDL_19_5_0_s50
  · exact computeLDL_19_5_1_s50
  · exact computeLDL_19_5_2_s50
  · exact computeLDL_19_5_3_s50
  · exact computeLDL_19_5_4_s50
  · exact computeLDL_19_5_5_s50
  · exact computeLDL_19_5_6_s50
  · exact computeLDL_19_5_7_s50
  · exact computeLDL_19_5_8_s50
  · exact computeLDL_19_5_9_s50
  · exact computeLDL_19_6_0_s50
  · exact computeLDL_19_6_1_s50
  · exact computeLDL_19_6_2_s50
  · exact computeLDL_19_6_3_s50
  · exact computeLDL_19_6_4_s50
  · exact computeLDL_19_6_5_s50
  · exact computeLDL_19_6_6_s50
  · exact computeLDL_19_6_7_s50
  · exact computeLDL_19_6_8_s50
  · exact computeLDL_19_6_9_s50
  · exact computeLDL_19_7_0_s50
  · exact computeLDL_19_7_1_s50
  · exact computeLDL_19_7_2_s50
  · exact computeLDL_19_7_3_s50
  · exact computeLDL_19_7_4_s50
  · exact computeLDL_19_7_5_s50
  · exact computeLDL_19_7_6_s50
  · exact computeLDL_19_7_7_s50
  · exact computeLDL_19_7_8_s50
  · exact computeLDL_19_7_9_s50
  · exact computeLDL_19_8_0_s50
  · exact computeLDL_19_8_1_s50
  · exact computeLDL_19_8_2_s50
  · exact computeLDL_19_8_3_s50
  · exact computeLDL_19_8_4_s50
  · exact computeLDL_19_8_5_s50
  · exact computeLDL_19_8_6_s50
  · exact computeLDL_19_8_7_s50
  · exact computeLDL_19_8_8_s50
  · exact computeLDL_19_8_9_s50
  · exact computeLDL_19_9_0_s50
  · exact computeLDL_19_9_1_s50
  · exact computeLDL_19_9_2_s50
  · exact computeLDL_19_9_3_s50
  · exact computeLDL_19_9_4_s50
  · exact computeLDL_19_9_5_s50
  · exact computeLDL_19_9_6_s50
  · exact computeLDL_19_9_7_s50
  · exact computeLDL_19_9_8_s50
  · exact computeLDL_19_9_9_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_19_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_19_s50_oai
