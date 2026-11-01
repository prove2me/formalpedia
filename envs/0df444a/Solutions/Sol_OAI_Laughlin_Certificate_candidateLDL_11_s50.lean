-- Prove2me | solution 1 for OAI.Laughlin.Certificate.candidateLDL_11_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-31T23:31:15.2352+00:00
-- url     : https://prove2.me/submissions/c992d6aa-b875-44aa-ad0c-1defd91d5ddf

import Mathlib
import Definitions.Def_OAIQ050L000
import Definitions.Def_OAIQ050L001
import Definitions.Def_OAIQ050L002
import Definitions.Def_OAIQ050L003
import Definitions.Def_OAIQ050L005
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_5_5_s50

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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_ComputeLDL11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_11_0_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_LDLData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_11_s50_oai : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 =
    lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_11_0_0
  · exact computeLDL_11_0_1
  · exact computeLDL_11_0_2
  · exact computeLDL_11_0_3
  · exact computeLDL_11_0_4
  · exact computeLDL_11_0_5
  · exact computeLDL_11_1_0
  · exact computeLDL_11_1_1
  · exact computeLDL_11_1_2
  · exact computeLDL_11_1_3
  · exact computeLDL_11_1_4
  · exact computeLDL_11_1_5
  · exact computeLDL_11_2_0
  · exact computeLDL_11_2_1
  · exact computeLDL_11_2_2
  · exact computeLDL_11_2_3
  · exact computeLDL_11_2_4
  · exact computeLDL_11_2_5
  · exact computeLDL_11_3_0
  · exact computeLDL_11_3_1
  · exact computeLDL_11_3_2
  · exact computeLDL_11_3_3
  · exact computeLDL_11_3_4
  · exact computeLDL_11_3_5
  · exact computeLDL_11_4_0
  · exact computeLDL_11_4_1
  · exact computeLDL_11_4_2
  · exact computeLDL_11_4_3
  · exact computeLDL_11_4_4
  · exact computeLDL_11_4_5
  · exact computeLDL_11_5_0
  · exact computeLDL_11_5_1
  · exact computeLDL_11_5_2
  · exact computeLDL_11_5_3
  · exact computeLDL_11_5_4
  · exact computeLDL_11_5_5_s50

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.candidateLDL_11_s50_oai := @OAI.Laughlin.Certificate.candidateLDL_11_s50_oai
