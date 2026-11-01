-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_17_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:34:21.271946+00:00
-- url     : https://prove2.me/submissions/e21666ff-b07d-441d-a303-63949a1c48d1

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_1_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_2_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_3_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_4_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_5_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_6_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_7_8_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_17_8_8_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_17_0_0 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 0 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_1 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 1 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_2 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 2 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_3 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 3 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_4 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 4 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_5 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 5 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_6 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 6 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_7 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 7 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_0_8 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 0 8 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 0 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_17_1_0 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 0 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_1 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 1 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_2 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 2 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_3 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 3 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_4 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 4 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_5 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 5 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_6 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 6 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_17_1_7 : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 1 7 =
    (lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose) 1 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData17
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_17_s50_oai : MatrixCompute.compressed 17 candidateY_17 candidateZ_17 =
    lower_17 * Matrix.diagonal pivots_17 * lower_17.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_17_0_0
  · exact computeLDL_17_0_1
  · exact computeLDL_17_0_2
  · exact computeLDL_17_0_3
  · exact computeLDL_17_0_4
  · exact computeLDL_17_0_5
  · exact computeLDL_17_0_6
  · exact computeLDL_17_0_7
  · exact computeLDL_17_0_8
  · exact computeLDL_17_1_0
  · exact computeLDL_17_1_1
  · exact computeLDL_17_1_2
  · exact computeLDL_17_1_3
  · exact computeLDL_17_1_4
  · exact computeLDL_17_1_5
  · exact computeLDL_17_1_6
  · exact computeLDL_17_1_7
  · exact computeLDL_17_1_8_s50
  · exact computeLDL_17_2_0_s50
  · exact computeLDL_17_2_1_s50
  · exact computeLDL_17_2_2_s50
  · exact computeLDL_17_2_3_s50
  · exact computeLDL_17_2_4_s50
  · exact computeLDL_17_2_5_s50
  · exact computeLDL_17_2_6_s50
  · exact computeLDL_17_2_7_s50
  · exact computeLDL_17_2_8_s50
  · exact computeLDL_17_3_0_s50
  · exact computeLDL_17_3_1_s50
  · exact computeLDL_17_3_2_s50
  · exact computeLDL_17_3_3_s50
  · exact computeLDL_17_3_4_s50
  · exact computeLDL_17_3_5_s50
  · exact computeLDL_17_3_6_s50
  · exact computeLDL_17_3_7_s50
  · exact computeLDL_17_3_8_s50
  · exact computeLDL_17_4_0_s50
  · exact computeLDL_17_4_1_s50
  · exact computeLDL_17_4_2_s50
  · exact computeLDL_17_4_3_s50
  · exact computeLDL_17_4_4_s50
  · exact computeLDL_17_4_5_s50
  · exact computeLDL_17_4_6_s50
  · exact computeLDL_17_4_7_s50
  · exact computeLDL_17_4_8_s50
  · exact computeLDL_17_5_0_s50
  · exact computeLDL_17_5_1_s50
  · exact computeLDL_17_5_2_s50
  · exact computeLDL_17_5_3_s50
  · exact computeLDL_17_5_4_s50
  · exact computeLDL_17_5_5_s50
  · exact computeLDL_17_5_6_s50
  · exact computeLDL_17_5_7_s50
  · exact computeLDL_17_5_8_s50
  · exact computeLDL_17_6_0_s50
  · exact computeLDL_17_6_1_s50
  · exact computeLDL_17_6_2_s50
  · exact computeLDL_17_6_3_s50
  · exact computeLDL_17_6_4_s50
  · exact computeLDL_17_6_5_s50
  · exact computeLDL_17_6_6_s50
  · exact computeLDL_17_6_7_s50
  · exact computeLDL_17_6_8_s50
  · exact computeLDL_17_7_0_s50
  · exact computeLDL_17_7_1_s50
  · exact computeLDL_17_7_2_s50
  · exact computeLDL_17_7_3_s50
  · exact computeLDL_17_7_4_s50
  · exact computeLDL_17_7_5_s50
  · exact computeLDL_17_7_6_s50
  · exact computeLDL_17_7_7_s50
  · exact computeLDL_17_7_8_s50
  · exact computeLDL_17_8_0_s50
  · exact computeLDL_17_8_1_s50
  · exact computeLDL_17_8_2_s50
  · exact computeLDL_17_8_3_s50
  · exact computeLDL_17_8_4_s50
  · exact computeLDL_17_8_5_s50
  · exact computeLDL_17_8_6_s50
  · exact computeLDL_17_8_7_s50
  · exact computeLDL_17_8_8_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_17_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_17_s50_oai
