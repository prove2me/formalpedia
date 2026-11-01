-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_15_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:33:01.86055+00:00
-- url     : https://prove2.me/submissions/622f08aa-967f-4ed2-a5a6-e7b91c37ea66

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L004
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_1_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_2_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_3_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_4_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_5_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_6_7_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_0_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_1_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_2_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_3_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_4_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_5_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_6_s50
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_15_7_7_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL00Batch15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_0_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_0_7 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 0 7 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 0 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL01Batch15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_15_1_0 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 0 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_1 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 1 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_2 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 2 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_3 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 3 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_4 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 4 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_5 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 5 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_15_1_6 : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 1 6 =
    (lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose) 1 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_15_s50_oai : MatrixCompute.compressed 15 candidateY_15 candidateZ_15 =
    lower_15 * Matrix.diagonal pivots_15 * lower_15.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_15_0_0
  · exact computeLDL_15_0_1
  · exact computeLDL_15_0_2
  · exact computeLDL_15_0_3
  · exact computeLDL_15_0_4
  · exact computeLDL_15_0_5
  · exact computeLDL_15_0_6
  · exact computeLDL_15_0_7
  · exact computeLDL_15_1_0
  · exact computeLDL_15_1_1
  · exact computeLDL_15_1_2
  · exact computeLDL_15_1_3
  · exact computeLDL_15_1_4
  · exact computeLDL_15_1_5
  · exact computeLDL_15_1_6
  · exact computeLDL_15_1_7_s50
  · exact computeLDL_15_2_0_s50
  · exact computeLDL_15_2_1_s50
  · exact computeLDL_15_2_2_s50
  · exact computeLDL_15_2_3_s50
  · exact computeLDL_15_2_4_s50
  · exact computeLDL_15_2_5_s50
  · exact computeLDL_15_2_6_s50
  · exact computeLDL_15_2_7_s50
  · exact computeLDL_15_3_0_s50
  · exact computeLDL_15_3_1_s50
  · exact computeLDL_15_3_2_s50
  · exact computeLDL_15_3_3_s50
  · exact computeLDL_15_3_4_s50
  · exact computeLDL_15_3_5_s50
  · exact computeLDL_15_3_6_s50
  · exact computeLDL_15_3_7_s50
  · exact computeLDL_15_4_0_s50
  · exact computeLDL_15_4_1_s50
  · exact computeLDL_15_4_2_s50
  · exact computeLDL_15_4_3_s50
  · exact computeLDL_15_4_4_s50
  · exact computeLDL_15_4_5_s50
  · exact computeLDL_15_4_6_s50
  · exact computeLDL_15_4_7_s50
  · exact computeLDL_15_5_0_s50
  · exact computeLDL_15_5_1_s50
  · exact computeLDL_15_5_2_s50
  · exact computeLDL_15_5_3_s50
  · exact computeLDL_15_5_4_s50
  · exact computeLDL_15_5_5_s50
  · exact computeLDL_15_5_6_s50
  · exact computeLDL_15_5_7_s50
  · exact computeLDL_15_6_0_s50
  · exact computeLDL_15_6_1_s50
  · exact computeLDL_15_6_2_s50
  · exact computeLDL_15_6_3_s50
  · exact computeLDL_15_6_4_s50
  · exact computeLDL_15_6_5_s50
  · exact computeLDL_15_6_6_s50
  · exact computeLDL_15_6_7_s50
  · exact computeLDL_15_7_0_s50
  · exact computeLDL_15_7_1_s50
  · exact computeLDL_15_7_2_s50
  · exact computeLDL_15_7_3_s50
  · exact computeLDL_15_7_4_s50
  · exact computeLDL_15_7_5_s50
  · exact computeLDL_15_7_6_s50
  · exact computeLDL_15_7_7_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_15_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_15_s50_oai
