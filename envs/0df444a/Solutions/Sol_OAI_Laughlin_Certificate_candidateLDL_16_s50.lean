-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_16_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:34:20.250672+00:00
-- url     : https://prove2.me/submissions/81985a4f-2d17-4f1f-adf2-0297d337463b

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_16_7_7_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_0_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_0_7 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 0 7 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_16_1_0 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 0 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_1 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 1 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_2 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 2 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_3 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 3 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_4 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 4 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_5 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 5 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_16_1_6 : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 1 6 =
    (lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_16_s50_oai : MatrixCompute.compressed 16 candidateY_16 candidateZ_16 =
    lower_16 * Matrix.diagonal pivots_16 * lower_16.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_16_0_0
  · exact computeLDL_16_0_1
  · exact computeLDL_16_0_2
  · exact computeLDL_16_0_3
  · exact computeLDL_16_0_4
  · exact computeLDL_16_0_5
  · exact computeLDL_16_0_6
  · exact computeLDL_16_0_7
  · exact computeLDL_16_1_0
  · exact computeLDL_16_1_1
  · exact computeLDL_16_1_2
  · exact computeLDL_16_1_3
  · exact computeLDL_16_1_4
  · exact computeLDL_16_1_5
  · exact computeLDL_16_1_6
  · exact computeLDL_16_1_7_s50
  · exact computeLDL_16_2_0_s50
  · exact computeLDL_16_2_1_s50
  · exact computeLDL_16_2_2_s50
  · exact computeLDL_16_2_3_s50
  · exact computeLDL_16_2_4_s50
  · exact computeLDL_16_2_5_s50
  · exact computeLDL_16_2_6_s50
  · exact computeLDL_16_2_7_s50
  · exact computeLDL_16_3_0_s50
  · exact computeLDL_16_3_1_s50
  · exact computeLDL_16_3_2_s50
  · exact computeLDL_16_3_3_s50
  · exact computeLDL_16_3_4_s50
  · exact computeLDL_16_3_5_s50
  · exact computeLDL_16_3_6_s50
  · exact computeLDL_16_3_7_s50
  · exact computeLDL_16_4_0_s50
  · exact computeLDL_16_4_1_s50
  · exact computeLDL_16_4_2_s50
  · exact computeLDL_16_4_3_s50
  · exact computeLDL_16_4_4_s50
  · exact computeLDL_16_4_5_s50
  · exact computeLDL_16_4_6_s50
  · exact computeLDL_16_4_7_s50
  · exact computeLDL_16_5_0_s50
  · exact computeLDL_16_5_1_s50
  · exact computeLDL_16_5_2_s50
  · exact computeLDL_16_5_3_s50
  · exact computeLDL_16_5_4_s50
  · exact computeLDL_16_5_5_s50
  · exact computeLDL_16_5_6_s50
  · exact computeLDL_16_5_7_s50
  · exact computeLDL_16_6_0_s50
  · exact computeLDL_16_6_1_s50
  · exact computeLDL_16_6_2_s50
  · exact computeLDL_16_6_3_s50
  · exact computeLDL_16_6_4_s50
  · exact computeLDL_16_6_5_s50
  · exact computeLDL_16_6_6_s50
  · exact computeLDL_16_6_7_s50
  · exact computeLDL_16_7_0_s50
  · exact computeLDL_16_7_1_s50
  · exact computeLDL_16_7_2_s50
  · exact computeLDL_16_7_3_s50
  · exact computeLDL_16_7_4_s50
  · exact computeLDL_16_7_5_s50
  · exact computeLDL_16_7_6_s50
  · exact computeLDL_16_7_7_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_16_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_16_s50_oai
