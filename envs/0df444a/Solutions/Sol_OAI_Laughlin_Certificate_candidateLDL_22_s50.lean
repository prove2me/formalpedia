-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_22_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:38:42.947426+00:00
-- url     : https://prove2.me/submissions/f8b72f54-ec8a-47e9-9df1-c5daac897f7f

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_0_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_10_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_1_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_2_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_3_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_4_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_5_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_6_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_7_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_8_9_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_10_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_22_9_9_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_0_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_0_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_1_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_1_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL02Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_2_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_22_s50_oai : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 =
    lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_22_0_0
  · exact computeLDL_22_0_1
  · exact computeLDL_22_0_2
  · exact computeLDL_22_0_3
  · exact computeLDL_22_0_4
  · exact computeLDL_22_0_5
  · exact computeLDL_22_0_6
  · exact computeLDL_22_0_7
  · exact computeLDL_22_0_8
  · exact computeLDL_22_0_9
  · exact computeLDL_22_0_10_s50
  · exact computeLDL_22_1_0
  · exact computeLDL_22_1_1
  · exact computeLDL_22_1_2
  · exact computeLDL_22_1_3
  · exact computeLDL_22_1_4
  · exact computeLDL_22_1_5
  · exact computeLDL_22_1_6
  · exact computeLDL_22_1_7
  · exact computeLDL_22_1_8
  · exact computeLDL_22_1_9
  · exact computeLDL_22_1_10_s50
  · exact computeLDL_22_2_0
  · exact computeLDL_22_2_1_s50
  · exact computeLDL_22_2_2_s50
  · exact computeLDL_22_2_3_s50
  · exact computeLDL_22_2_4_s50
  · exact computeLDL_22_2_5_s50
  · exact computeLDL_22_2_6_s50
  · exact computeLDL_22_2_7_s50
  · exact computeLDL_22_2_8_s50
  · exact computeLDL_22_2_9_s50
  · exact computeLDL_22_2_10_s50
  · exact computeLDL_22_3_0_s50
  · exact computeLDL_22_3_1_s50
  · exact computeLDL_22_3_2_s50
  · exact computeLDL_22_3_3_s50
  · exact computeLDL_22_3_4_s50
  · exact computeLDL_22_3_5_s50
  · exact computeLDL_22_3_6_s50
  · exact computeLDL_22_3_7_s50
  · exact computeLDL_22_3_8_s50
  · exact computeLDL_22_3_9_s50
  · exact computeLDL_22_3_10_s50
  · exact computeLDL_22_4_0_s50
  · exact computeLDL_22_4_1_s50
  · exact computeLDL_22_4_2_s50
  · exact computeLDL_22_4_3_s50
  · exact computeLDL_22_4_4_s50
  · exact computeLDL_22_4_5_s50
  · exact computeLDL_22_4_6_s50
  · exact computeLDL_22_4_7_s50
  · exact computeLDL_22_4_8_s50
  · exact computeLDL_22_4_9_s50
  · exact computeLDL_22_4_10_s50
  · exact computeLDL_22_5_0_s50
  · exact computeLDL_22_5_1_s50
  · exact computeLDL_22_5_2_s50
  · exact computeLDL_22_5_3_s50
  · exact computeLDL_22_5_4_s50
  · exact computeLDL_22_5_5_s50
  · exact computeLDL_22_5_6_s50
  · exact computeLDL_22_5_7_s50
  · exact computeLDL_22_5_8_s50
  · exact computeLDL_22_5_9_s50
  · exact computeLDL_22_5_10_s50
  · exact computeLDL_22_6_0_s50
  · exact computeLDL_22_6_1_s50
  · exact computeLDL_22_6_2_s50
  · exact computeLDL_22_6_3_s50
  · exact computeLDL_22_6_4_s50
  · exact computeLDL_22_6_5_s50
  · exact computeLDL_22_6_6_s50
  · exact computeLDL_22_6_7_s50
  · exact computeLDL_22_6_8_s50
  · exact computeLDL_22_6_9_s50
  · exact computeLDL_22_6_10_s50
  · exact computeLDL_22_7_0_s50
  · exact computeLDL_22_7_1_s50
  · exact computeLDL_22_7_2_s50
  · exact computeLDL_22_7_3_s50
  · exact computeLDL_22_7_4_s50
  · exact computeLDL_22_7_5_s50
  · exact computeLDL_22_7_6_s50
  · exact computeLDL_22_7_7_s50
  · exact computeLDL_22_7_8_s50
  · exact computeLDL_22_7_9_s50
  · exact computeLDL_22_7_10_s50
  · exact computeLDL_22_8_0_s50
  · exact computeLDL_22_8_1_s50
  · exact computeLDL_22_8_2_s50
  · exact computeLDL_22_8_3_s50
  · exact computeLDL_22_8_4_s50
  · exact computeLDL_22_8_5_s50
  · exact computeLDL_22_8_6_s50
  · exact computeLDL_22_8_7_s50
  · exact computeLDL_22_8_8_s50
  · exact computeLDL_22_8_9_s50
  · exact computeLDL_22_8_10_s50
  · exact computeLDL_22_9_0_s50
  · exact computeLDL_22_9_1_s50
  · exact computeLDL_22_9_2_s50
  · exact computeLDL_22_9_3_s50
  · exact computeLDL_22_9_4_s50
  · exact computeLDL_22_9_5_s50
  · exact computeLDL_22_9_6_s50
  · exact computeLDL_22_9_7_s50
  · exact computeLDL_22_9_8_s50
  · exact computeLDL_22_9_9_s50
  · exact computeLDL_22_9_10_s50
  · exact computeLDL_22_10_0_s50
  · exact computeLDL_22_10_1_s50
  · exact computeLDL_22_10_2_s50
  · exact computeLDL_22_10_3_s50
  · exact computeLDL_22_10_4_s50
  · exact computeLDL_22_10_5_s50
  · exact computeLDL_22_10_6_s50
  · exact computeLDL_22_10_7_s50
  · exact computeLDL_22_10_8_s50
  · exact computeLDL_22_10_9_s50
  · exact computeLDL_22_10_10_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_22_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_22_s50_oai
