-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_11_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:31:10.057987+00:00
-- url     : https://prove2.me/submissions/0a220203-edbb-498c-8131-177f1d54116e

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_11_11
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_1_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_3_11
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_3_9
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_5_9
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_7_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_11_9_11
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_0_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_0_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_0_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_0_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_2_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_2_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_2_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_3_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_3_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_4_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_4_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_4_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_11_5_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_11_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_11_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_11_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_11_11_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_1_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_1_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_1_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_3_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_5_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_7_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_3_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_11_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_11_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_11_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_5_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_5_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_5_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_11_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_7_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_11_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_11_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_11_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_11_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_11_9_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_eq_integral

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_11 : GramCompute.quadruples 11 = [(0,1,2,9), (0,1,3,8), (0,1,4,7), (0,1,5,6), (0,2,3,7), (0,2,4,6), (0,3,4,5), (1,2,3,6), (1,2,4,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_11_1_5 : GramCompute.ZFast 11 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_9 : GramCompute.ZFast 11 1 9 = (-453600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_1_11 : GramCompute.ZFast 11 1 11 = (9979200 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_3 : GramCompute.ZFast 11 3 3 = (241920 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_3_7 : GramCompute.ZFast 11 3 7 = (-60480 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_7 : GramCompute.ZFast 11 5 7 = (-75600 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_5_11 : GramCompute.ZFast 11 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_7_9 : GramCompute.ZFast 11 7 9 = (-158760 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_7_11 : GramCompute.ZFast 11 7 11 = (-623700 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

theorem computeGram_11_9_9 : GramCompute.ZFast 11 9 9 = (266490 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_11]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_MatrixCompute
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL050511
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_11_5_5 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 5 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeLDL_11_0_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_0_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 0 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 0 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_1_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 1 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_2_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 2 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_3_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 3 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_0 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 0 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_2 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 2 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_4_4 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 4 4 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_1 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 1 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_11_5_3 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 5 3 =
    (lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_1_1 : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[1]!) =
    (188801936548074640026166409356538174154958994027839488000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_1_3 : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[3]!) =
    (-161492551692087858517794755610188140351744290919903395840000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_1_5 : RowCompute.yRowIntegralFast 11 1 1 (RowCompute.rows[5]!) =
    (-35115420256530926495897573237813410058106053459322077184000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_3_1 : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[1]!) =
    (-838032958672181173297092999309932175987037328061235200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_3_3 : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[3]!) =
    (35918981384538503116977733754961600471413977832969207808000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_3_5 : RowCompute.yRowIntegralFast 11 1 3 (RowCompute.rows[5]!) =
    (3267666253525117671842401193154117285182667844856315904000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_5_0 : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[0]!) =
    (22161555571705251936872894305425946072316484646971899904000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_5_2 : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[2]!) =
    (-19178356394482081013323905907604165968753902870054567936000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_5_4 : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[4]!) =
    (158576031092963877493653605626522502493824905434365952000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_5_6 : RowCompute.yRowIntegralFast 11 1 5 (RowCompute.rows[6]!) =
    (-60971925946082659739796338466785798093698002239619072000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_7_1 : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[1]!) =
    (10629824643813890553906150130784840915554563694107033600000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_7_3 : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[3]!) =
    (10154179987415264579003464103984284384392418155609194496000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_7_5 : RowCompute.yRowIntegralFast 11 1 7 (RowCompute.rows[5]!) =
    (-2928207253228515422603957049850146128119439446096478208000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_9_0 : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[0]!) =
    (-45602730338334488893636037915717308427123807790525579264000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_9_2 : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[2]!) =
    (-63540942190744224614618792228246482884726318979444899840000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_9_5 : RowCompute.yRowIntegralFast 11 1 9 (RowCompute.rows[5]!) =
    (-18758181480393526637102698540557121829300993187328819200000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow112
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_1_11_0 : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[0]!) =
    (208909669036874329446228303412831270235588717522932727808000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_11_2 : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[2]!) =
    (415179680129717535936122509111093744551896134972216442880000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_11_4 : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[4]!) =
    (15201154142663099871376092474827408880288081779380715520000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_1_11_6 : RowCompute.yRowIntegralFast 11 1 11 (RowCompute.rows[6]!) =
    (6090016022914256954179649770019926614088794438358794240000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_3_1 : RowCompute.yRowIntegralFast 11 3 3 (RowCompute.rows[1]!) =
    (4404198226324057979170734594700571471887601727071846400000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_3_3 : RowCompute.yRowIntegralFast 11 3 3 (RowCompute.rows[3]!) =
    (-7049413884075317526577829424157184516231346675454574592000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_3_5 : RowCompute.yRowIntegralFast 11 3 3 (RowCompute.rows[5]!) =
    (-643889442281372120124916372768311303785529008672106086400000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_5_0 : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[0]!) =
    (-1208773702633481130004103946409083364260543193864470528000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_5_2 : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[2]!) =
    (7201774151894466401268335874222293203626243336123187200000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_5_4 : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[4]!) =
    (184140347228940821900314622330660870584003657413427200000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_5_6 : RowCompute.yRowIntegralFast 11 3 5 (RowCompute.rows[6]!) =
    (8978918400224346326071717312141253296454663871135744000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_7_2 : RowCompute.yRowIntegralFast 11 3 7 (RowCompute.rows[2]!) =
    (-8044840461685050849968322139599587739134066178080007782400000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_7_4 : RowCompute.yRowIntegralFast 11 3 7 (RowCompute.rows[4]!) =
    (-139091500690990069734061185877742482844282380653428736000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_7_6 : RowCompute.yRowIntegralFast 11 3 7 (RowCompute.rows[6]!) =
    (-149845554231977708554912559088293077793167578009226444800000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_9_1 : RowCompute.yRowIntegralFast 11 3 9 (RowCompute.rows[1]!) =
    (18538538832166388658457949709979265705505490189103923200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_9_3 : RowCompute.yRowIntegralFast 11 3 9 (RowCompute.rows[3]!) =
    (3841847074751699304558936921282126751327497810280552857600000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_9_5 : RowCompute.yRowIntegralFast 11 3 9 (RowCompute.rows[5]!) =
    (4747205409257050334583818829056393173793643841792140902400000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow113
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_3_11_0 : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[0]!) =
    (1334419635460864113188668679581084484315803833147064320000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_11_2 : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[2]!) =
    (-7677545277836763793762668118817810399932606204858073088000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_11_4 : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[4]!) =
    (3625662227315652578923349232173263676164629888787021824000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_3_11_6 : RowCompute.yRowIntegralFast 11 3 11 (RowCompute.rows[6]!) =
    (12604718826858728667163107584604338594856349502275584000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_5_1 : RowCompute.yRowIntegralFast 11 5 5 (RowCompute.rows[1]!) =
    (-1366124749782041395239449825445665236196055746347008000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_5_3 : RowCompute.yRowIntegralFast 11 5 5 (RowCompute.rows[3]!) =
    (-666840194475290935494031723128751364068421682736398336000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_5_5 : RowCompute.yRowIntegralFast 11 5 5 (RowCompute.rows[5]!) =
    (-165789821854245912284864660386264170622268753389289472000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_7_1 : RowCompute.yRowIntegralFast 11 5 7 (RowCompute.rows[1]!) =
    (-4375466433774225708241661845128455916448321068072960000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_7_3 : RowCompute.yRowIntegralFast 11 5 7 (RowCompute.rows[3]!) =
    (-1881992598927931691602392906416639845295736197002297344000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_7_5 : RowCompute.yRowIntegralFast 11 5 7 (RowCompute.rows[5]!) =
    (711643995252125575990655512287480020110358292411187200000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_9_0 : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[0]!) =
    (5606221486357660955779448714588023600589789503917391872000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_9_2 : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[2]!) =
    (-10617376574178618951443735285882079041866858659997286400000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_9_4 : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[4]!) =
    (42904795595361462881407652441991188990827554643378176000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_9_6 : RowCompute.yRowIntegralFast 11 5 9 (RowCompute.rows[6]!) =
    (39564846350591731496377177206613756743845778473091072000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_11_0 : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[0]!) =
    (-6661095354325417163995509632261387201773090681091260416000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_11_2 : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[2]!) =
    (55772064840338868687574049881867509735543454726839336960000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_11_4 : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[4]!) =
    (-2061710552732647711892056032318033772447677053531062272000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_5_11_6 : RowCompute.yRowIntegralFast 11 5 11 (RowCompute.rows[6]!) =
    (-610384553083287136788732467966426699293074625702920192000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow114
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_7_7_0 : RowCompute.yRowIntegralFast 11 7 7 (RowCompute.rows[0]!) =
    (-2588226275327575206182979647424659077173740200953643008000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_7_2 : RowCompute.yRowIntegralFast 11 7 7 (RowCompute.rows[2]!) =
    (-1346571666439240993152823374685633335585950793457886822400000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_7_5 : RowCompute.yRowIntegralFast 11 7 7 (RowCompute.rows[5]!) =
    (1108135500275310141651230563820236788967472364296287027200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_9_0 : RowCompute.yRowIntegralFast 11 7 9 (RowCompute.rows[0]!) =
    (-10945098134258301157150964611705323279998161401503809536000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_9_2 : RowCompute.yRowIntegralFast 11 7 9 (RowCompute.rows[2]!) =
    (-4896803245441794684008393298188079316297358189811833241600000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_9_4 : RowCompute.yRowIntegralFast 11 7 9 (RowCompute.rows[4]!) =
    (489031885098143181509199844747648057207266693226482892800000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_9_6 : RowCompute.yRowIntegralFast 11 7 9 (RowCompute.rows[6]!) =
    (-1027784325013598963600084513224960188531802538980147200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_11_1 : RowCompute.yRowIntegralFast 11 7 11 (RowCompute.rows[1]!) =
    (227858991317733984359469243298321634226263177330216140800000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_11_3 : RowCompute.yRowIntegralFast 11 7 11 (RowCompute.rows[3]!) =
    (-16962875410589050856078100082969213915033882794085318656000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_7_11_5 : RowCompute.yRowIntegralFast 11 7 11 (RowCompute.rows[5]!) =
    (-753280806882112499441353041748108224748005267056099328000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_9_0 : RowCompute.yRowIntegralFast 11 9 9 (RowCompute.rows[0]!) =
    (64846376697731414615127732291179481928983251006963004211200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_9_2 : RowCompute.yRowIntegralFast 11 9 9 (RowCompute.rows[2]!) =
    (22901521043461306232359457876968996613488175831744249856000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_9_4 : RowCompute.yRowIntegralFast 11 9 9 (RowCompute.rows[4]!) =
    (1103815965523995512833129115547429711662794919627666227200000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_9_6 : RowCompute.yRowIntegralFast 11 9 9 (RowCompute.rows[6]!) =
    (-435231449031901262759412737687685129677384323279355904000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_11_1 : RowCompute.yRowIntegralFast 11 9 11 (RowCompute.rows[1]!) =
    (-599097877235940608335365331628754384827381370505396224000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_11_3 : RowCompute.yRowIntegralFast 11 9 11 (RowCompute.rows[3]!) =
    (64109078532254694353539997313811767742371552212872593408000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_9_11_5 : RowCompute.yRowIntegralFast 11 9 11 (RowCompute.rows[5]!) =
    (116773312489460748630493797423089879549014319107670016000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_11_11_11_1 : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[1]!) =
    (3759834114105657339247232532691136516399959623755366400000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_11_11_3 : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[3]!) =
    (2971015326380784181796702359312719027241898763014910246912000000 : ℤ) := by
  decide +kernel

theorem computeRow_11_11_11_5 : RowCompute.yRowIntegralFast 11 11 11 (RowCompute.rows[5]!) =
    (189965276033806669960801735149717380833391259422432428032000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Basic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped BigOperators Matrix

theorem Y_expand (D r s : ℕ) : Y D r s =
    -(yRow D r s (rows[0]!) + (yRow D r s (rows[1]!) +
      (yRow D r s (rows[2]!) + (yRow D r s (rows[3]!) +
        (yRow D r s (rows[4]!) + (yRow D r s (rows[5]!) +
          (yRow D r s (rows[6]!) + 0))))))) / (10^14 : ℚ) := by rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_Operators_RationalPSD
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem rational_ldl_positive {n : ℕ} (A L : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : A = L * Matrix.diagonal d * L.transpose)
    (hd : ∀ i, 0 ≤ d i) : (A.map (Rat.castHom ℝ)).PosSemidef := by
  rw [h, Matrix.map_mul, Matrix.map_mul]
  have hdiag : (Matrix.diagonal d).map (Rat.castHom ℝ) =
      Matrix.diagonal (fun i => (d i : ℝ)) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have htrans : L.transpose.map (Rat.castHom ℝ) =
      (L.map (Rat.castHom ℝ)).conjTranspose := by
    ext i j
    simp
  rw [hdiag, htrans]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro i
  change (0 : ℝ) ≤ (d i : ℝ)
  exact_mod_cast hd i

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Integral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem rows_integral_bounds : ∀ row ∈ rows, row.1 ≤ 16 ∧
    ∀ e ∈ row.2.2, ∀ f ∈ row.2.2,
      e.1 + e.2.1 + (f.1 + f.2.1 - row.1) ≤ 24 := by
  decide +kernel

theorem source_yRow_eq_integral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegral D r s (rows[n]!) : ℚ) / arithmeticScale := by
  have hm : rows[n]! ∈ rows := by
    interval_cases n <;> decide +kernel
  exact yRow_eq_integral D r s _ (rows_integral_bounds _ hm).1 (rows_integral_bounds _ hm).2

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_FastChoose
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem U_eq_fast (c z T p : ℕ) : U c z T p = UFast c z T p := by
  simp only [U, UFast, Nat.choose_eq_fast_choose]

theorem V_eq_fast (r D T p j k : ℕ) : V r D T p j k = VFast r D T p j k := by
  simp only [V, VFast, U_eq_fast]

theorem yEntryIntegral_eq_fast (D r s t : ℕ) (e f : ℕ × ℕ × ℤ) :
    yEntryIntegral D r s t e f = yEntryIntegralFast D r s t e f := by
  simp only [yEntryIntegral, yEntryIntegralFast, V_eq_fast]

theorem yRowIntegral_eq_fast (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ)) :
    yRowIntegral D r s row = yRowIntegralFast D r s row := by
  simp only [yRowIntegral, yRowIntegralFast, yEntryIntegral_eq_fast]

theorem source_yRow_eq_fastIntegral (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (yRowIntegralFast D r s (rows[n]!) : ℚ) / arithmeticScale := by
  rw [source_yRow_eq_integral D r s n hn, yRowIntegral_eq_fast]

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_RowBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_yRow_eq_rowCompute (D r s n : ℕ) (hn : n < 7) :
    yRow D r s (rows[n]!) = (RowCompute.yRowIntegralFast D r s (RowCompute.rows[n]!) : ℚ) / arithmeticScale := by
  exact source_yRow_eq_fastIntegral D r s n hn

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_NumericBridge
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem Z_eq_gramCompute (D r s : ℕ) : Z D r s = GramCompute.ZFast D r s := by
  exact Z_eq_fast D r s

theorem compressedRational_eq_compute (D : ℕ) :
    compressedRational D = MatrixCompute.compressed D (errorRational D) (gramRational D) := by
  rfl

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FourBody_Symmetry
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem yEntry_swap (D r s t : ℕ) (e f : ℕ × ℕ × ℤ)
    (he : t ≤ e.1 + e.2.1) (hf : t ≤ f.1 + f.2.1) :
    yEntry D r s t e f = yEntry D s r t f e := by
  rcases e with ⟨p,j,a⟩
  rcases f with ⟨q,l,b⟩
  dsimp at he hf
  have hT : q+l+(p+j-t) = p+j+(q+l-t) := by omega
  simp only [yEntry, hT, Nat.add_comm s r]
  split_ifs <;> ring_nf

private theorem sum_add {Element : Type*} (xs : List Element) (f g : Element → ℚ) :
    (xs.map (fun x => f x + g x)).sum = (xs.map f).sum + (xs.map g).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.map_cons, List.sum_cons, ih]; ring

private theorem sum_swap {Element : Type*} (xs ys : List Element)
    (f : Element → Element → ℚ) :
    (xs.map (fun x => (ys.map (f x)).sum)).sum =
      (ys.map (fun y => (xs.map (fun x => f x y)).sum)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons, ih, sum_add]

theorem yRow_swap (D r s : ℕ) (row : ℕ × ℤ × List (ℕ × ℕ × ℤ))
    (h : ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1) :
    yRow D r s row = yRow D s r row := by
  unfold yRow
  rw [sum_swap]
  congr 1
  apply List.map_congr_left
  intro f hf
  congr 1
  apply List.map_congr_left
  intro e he
  exact yEntry_swap D r s row.1 e f (h e he) (h f hf)

theorem rows_valid : ∀ row ∈ rows, ∀ e ∈ row.2.2, row.1 ≤ e.1 + e.2.1 := by
  decide +kernel

theorem Y_symm (D r s : ℕ) : Y D r s = Y D s r := by
  unfold Y
  congr 3
  apply List.map_congr_left
  intro row hr
  exact yRow_swap D r s row (rows_valid row hr)

theorem Z_symm (D r s : ℕ) : Z D r s = Z D s r := by
  unfold Z
  congr 1
  apply List.map_congr_left
  intro A hA
  dsimp
  ring

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_11_1_1 : Y 11 1 1 = (15310420495743050456853357/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 1 0 (by decide),
    source_yRow_eq_rowCompute 11 1 1 1 (by decide),
    source_yRow_eq_rowCompute 11 1 1 2 (by decide),
    source_yRow_eq_rowCompute 11 1 1 3 (by decide),
    source_yRow_eq_rowCompute 11 1 1 4 (by decide),
    source_yRow_eq_rowCompute 11 1 1 5 (by decide),
    source_yRow_eq_rowCompute 11 1 1 6 (by decide),
    computeRow_11_1_1_0, computeRow_11_1_1_1, computeRow_11_1_1_2, computeRow_11_1_1_3, computeRow_11_1_1_4, computeRow_11_1_1_5, computeRow_11_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_3 : Y 11 1 3 = (-21091981152473935416162441/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 3 0 (by decide),
    source_yRow_eq_rowCompute 11 1 3 1 (by decide),
    source_yRow_eq_rowCompute 11 1 3 2 (by decide),
    source_yRow_eq_rowCompute 11 1 3 3 (by decide),
    source_yRow_eq_rowCompute 11 1 3 4 (by decide),
    source_yRow_eq_rowCompute 11 1 3 5 (by decide),
    source_yRow_eq_rowCompute 11 1 3 6 (by decide),
    computeRow_11_1_3_0, computeRow_11_1_3_1, computeRow_11_1_3_2, computeRow_11_1_3_3, computeRow_11_1_3_4, computeRow_11_1_3_5, computeRow_11_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_5 : Y 11 1 5 = (1759644912412486678804947/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 5 0 (by decide),
    source_yRow_eq_rowCompute 11 1 5 1 (by decide),
    source_yRow_eq_rowCompute 11 1 5 2 (by decide),
    source_yRow_eq_rowCompute 11 1 5 3 (by decide),
    source_yRow_eq_rowCompute 11 1 5 4 (by decide),
    source_yRow_eq_rowCompute 11 1 5 5 (by decide),
    source_yRow_eq_rowCompute 11 1 5 6 (by decide),
    computeRow_11_1_5_0, computeRow_11_1_5_1, computeRow_11_1_5_2, computeRow_11_1_5_3, computeRow_11_1_5_4, computeRow_11_1_5_5, computeRow_11_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_7 : Y 11 1 7 = (-7117902998608090523107887/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 7 0 (by decide),
    source_yRow_eq_rowCompute 11 1 7 1 (by decide),
    source_yRow_eq_rowCompute 11 1 7 2 (by decide),
    source_yRow_eq_rowCompute 11 1 7 3 (by decide),
    source_yRow_eq_rowCompute 11 1 7 4 (by decide),
    source_yRow_eq_rowCompute 11 1 7 5 (by decide),
    source_yRow_eq_rowCompute 11 1 7 6 (by decide),
    computeRow_11_1_7_0, computeRow_11_1_7_1, computeRow_11_1_7_2, computeRow_11_1_7_3, computeRow_11_1_7_4, computeRow_11_1_7_5, computeRow_11_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_9 : Y 11 1 9 = (2050140304557578762479287/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 9 0 (by decide),
    source_yRow_eq_rowCompute 11 1 9 1 (by decide),
    source_yRow_eq_rowCompute 11 1 9 2 (by decide),
    source_yRow_eq_rowCompute 11 1 9 3 (by decide),
    source_yRow_eq_rowCompute 11 1 9 4 (by decide),
    source_yRow_eq_rowCompute 11 1 9 5 (by decide),
    source_yRow_eq_rowCompute 11 1 9 6 (by decide),
    computeRow_11_1_9_0, computeRow_11_1_9_1, computeRow_11_1_9_2, computeRow_11_1_9_3, computeRow_11_1_9_4, computeRow_11_1_9_5, computeRow_11_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_1_11 : Y 11 1 11 = (-3816671070411211699962099/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 1 11 0 (by decide),
    source_yRow_eq_rowCompute 11 1 11 1 (by decide),
    source_yRow_eq_rowCompute 11 1 11 2 (by decide),
    source_yRow_eq_rowCompute 11 1 11 3 (by decide),
    source_yRow_eq_rowCompute 11 1 11 4 (by decide),
    source_yRow_eq_rowCompute 11 1 11 5 (by decide),
    source_yRow_eq_rowCompute 11 1 11 6 (by decide),
    computeRow_11_1_11_0, computeRow_11_1_11_1, computeRow_11_1_11_2, computeRow_11_1_11_3, computeRow_11_1_11_4, computeRow_11_1_11_5, computeRow_11_1_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_3 : Y 11 3 3 = (3139824493398164330092707/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 3 0 (by decide),
    source_yRow_eq_rowCompute 11 3 3 1 (by decide),
    source_yRow_eq_rowCompute 11 3 3 2 (by decide),
    source_yRow_eq_rowCompute 11 3 3 3 (by decide),
    source_yRow_eq_rowCompute 11 3 3 4 (by decide),
    source_yRow_eq_rowCompute 11 3 3 5 (by decide),
    source_yRow_eq_rowCompute 11 3 3 6 (by decide),
    computeRow_11_3_3_0, computeRow_11_3_3_1, computeRow_11_3_3_2, computeRow_11_3_3_3, computeRow_11_3_3_4, computeRow_11_3_3_5, computeRow_11_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_5 : Y 11 3 5 = (-110846050581407277067047/13421772800000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 5 0 (by decide),
    source_yRow_eq_rowCompute 11 3 5 1 (by decide),
    source_yRow_eq_rowCompute 11 3 5 2 (by decide),
    source_yRow_eq_rowCompute 11 3 5 3 (by decide),
    source_yRow_eq_rowCompute 11 3 5 4 (by decide),
    source_yRow_eq_rowCompute 11 3 5 5 (by decide),
    source_yRow_eq_rowCompute 11 3 5 6 (by decide),
    computeRow_11_3_5_0, computeRow_11_3_5_1, computeRow_11_3_5_2, computeRow_11_3_5_3, computeRow_11_3_5_4, computeRow_11_3_5_5, computeRow_11_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_7 : Y 11 3 7 = (-120000452149124136234801/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 7 0 (by decide),
    source_yRow_eq_rowCompute 11 3 7 1 (by decide),
    source_yRow_eq_rowCompute 11 3 7 2 (by decide),
    source_yRow_eq_rowCompute 11 3 7 3 (by decide),
    source_yRow_eq_rowCompute 11 3 7 4 (by decide),
    source_yRow_eq_rowCompute 11 3 7 5 (by decide),
    source_yRow_eq_rowCompute 11 3 7 6 (by decide),
    computeRow_11_3_7_0, computeRow_11_3_7_1, computeRow_11_3_7_2, computeRow_11_3_7_3, computeRow_11_3_7_4, computeRow_11_3_7_5, computeRow_11_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_9 : Y 11 3 9 = (-804905973848069092119267/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 9 0 (by decide),
    source_yRow_eq_rowCompute 11 3 9 1 (by decide),
    source_yRow_eq_rowCompute 11 3 9 2 (by decide),
    source_yRow_eq_rowCompute 11 3 9 3 (by decide),
    source_yRow_eq_rowCompute 11 3 9 4 (by decide),
    source_yRow_eq_rowCompute 11 3 9 5 (by decide),
    source_yRow_eq_rowCompute 11 3 9 6 (by decide),
    computeRow_11_3_9_0, computeRow_11_3_9_1, computeRow_11_3_9_2, computeRow_11_3_9_3, computeRow_11_3_9_4, computeRow_11_3_9_5, computeRow_11_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_3_11 : Y 11 3 11 = (-488664944191263381981813/20971520000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 3 11 0 (by decide),
    source_yRow_eq_rowCompute 11 3 11 1 (by decide),
    source_yRow_eq_rowCompute 11 3 11 2 (by decide),
    source_yRow_eq_rowCompute 11 3 11 3 (by decide),
    source_yRow_eq_rowCompute 11 3 11 4 (by decide),
    source_yRow_eq_rowCompute 11 3 11 5 (by decide),
    source_yRow_eq_rowCompute 11 3 11 6 (by decide),
    computeRow_11_3_11_0, computeRow_11_3_11_1, computeRow_11_3_11_2, computeRow_11_3_11_3, computeRow_11_3_11_4, computeRow_11_3_11_5, computeRow_11_3_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_5 : Y 11 5 5 = (186561496958160530399967/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 5 0 (by decide),
    source_yRow_eq_rowCompute 11 5 5 1 (by decide),
    source_yRow_eq_rowCompute 11 5 5 2 (by decide),
    source_yRow_eq_rowCompute 11 5 5 3 (by decide),
    source_yRow_eq_rowCompute 11 5 5 4 (by decide),
    source_yRow_eq_rowCompute 11 5 5 5 (by decide),
    source_yRow_eq_rowCompute 11 5 5 6 (by decide),
    computeRow_11_5_5_0, computeRow_11_5_5_1, computeRow_11_5_5_2, computeRow_11_5_5_3, computeRow_11_5_5_4, computeRow_11_5_5_5, computeRow_11_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_7 : Y 11 5 7 = (-132022995280028243088831/67108864000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 7 0 (by decide),
    source_yRow_eq_rowCompute 11 5 7 1 (by decide),
    source_yRow_eq_rowCompute 11 5 7 2 (by decide),
    source_yRow_eq_rowCompute 11 5 7 3 (by decide),
    source_yRow_eq_rowCompute 11 5 7 4 (by decide),
    source_yRow_eq_rowCompute 11 5 7 5 (by decide),
    source_yRow_eq_rowCompute 11 5 7 6 (by decide),
    computeRow_11_5_7_0, computeRow_11_5_7_1, computeRow_11_5_7_2, computeRow_11_5_7_3, computeRow_11_5_7_4, computeRow_11_5_7_5, computeRow_11_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_9 : Y 11 5 9 = (39011604836809336804287/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 9 0 (by decide),
    source_yRow_eq_rowCompute 11 5 9 1 (by decide),
    source_yRow_eq_rowCompute 11 5 9 2 (by decide),
    source_yRow_eq_rowCompute 11 5 9 3 (by decide),
    source_yRow_eq_rowCompute 11 5 9 4 (by decide),
    source_yRow_eq_rowCompute 11 5 9 5 (by decide),
    source_yRow_eq_rowCompute 11 5 9 6 (by decide),
    computeRow_11_5_9_0, computeRow_11_5_9_1, computeRow_11_5_9_2, computeRow_11_5_9_3, computeRow_11_5_9_4, computeRow_11_5_9_5, computeRow_11_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_5_11 : Y 11 5 11 = (-536635508982633719381547/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 5 11 0 (by decide),
    source_yRow_eq_rowCompute 11 5 11 1 (by decide),
    source_yRow_eq_rowCompute 11 5 11 2 (by decide),
    source_yRow_eq_rowCompute 11 5 11 3 (by decide),
    source_yRow_eq_rowCompute 11 5 11 4 (by decide),
    source_yRow_eq_rowCompute 11 5 11 5 (by decide),
    source_yRow_eq_rowCompute 11 5 11 6 (by decide),
    computeRow_11_5_11_0, computeRow_11_5_11_1, computeRow_11_5_11_2, computeRow_11_5_11_3, computeRow_11_5_11_4, computeRow_11_5_11_5, computeRow_11_5_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_7 : Y 11 7 7 = (53081184869685889157043/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 7 0 (by decide),
    source_yRow_eq_rowCompute 11 7 7 1 (by decide),
    source_yRow_eq_rowCompute 11 7 7 2 (by decide),
    source_yRow_eq_rowCompute 11 7 7 3 (by decide),
    source_yRow_eq_rowCompute 11 7 7 4 (by decide),
    source_yRow_eq_rowCompute 11 7 7 5 (by decide),
    source_yRow_eq_rowCompute 11 7 7 6 (by decide),
    computeRow_11_7_7_0, computeRow_11_7_7_1, computeRow_11_7_7_2, computeRow_11_7_7_3, computeRow_11_7_7_4, computeRow_11_7_7_5, computeRow_11_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_9 : Y 11 7 9 = (581826960578730870868149/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 9 0 (by decide),
    source_yRow_eq_rowCompute 11 7 9 1 (by decide),
    source_yRow_eq_rowCompute 11 7 9 2 (by decide),
    source_yRow_eq_rowCompute 11 7 9 3 (by decide),
    source_yRow_eq_rowCompute 11 7 9 4 (by decide),
    source_yRow_eq_rowCompute 11 7 9 5 (by decide),
    source_yRow_eq_rowCompute 11 7 9 6 (by decide),
    computeRow_11_7_9_0, computeRow_11_7_9_1, computeRow_11_7_9_2, computeRow_11_7_9_3, computeRow_11_7_9_4, computeRow_11_7_9_5, computeRow_11_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_7_11 : Y 11 7 11 = (48169578758531066711919/20971520000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 7 11 0 (by decide),
    source_yRow_eq_rowCompute 11 7 11 1 (by decide),
    source_yRow_eq_rowCompute 11 7 11 2 (by decide),
    source_yRow_eq_rowCompute 11 7 11 3 (by decide),
    source_yRow_eq_rowCompute 11 7 11 4 (by decide),
    source_yRow_eq_rowCompute 11 7 11 5 (by decide),
    source_yRow_eq_rowCompute 11 7 11 6 (by decide),
    computeRow_11_7_11_0, computeRow_11_7_11_1, computeRow_11_7_11_2, computeRow_11_7_11_3, computeRow_11_7_11_4, computeRow_11_7_11_5, computeRow_11_7_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_9_9 : Y 11 9 9 = (-985704999590345844614157/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 9 9 0 (by decide),
    source_yRow_eq_rowCompute 11 9 9 1 (by decide),
    source_yRow_eq_rowCompute 11 9 9 2 (by decide),
    source_yRow_eq_rowCompute 11 9 9 3 (by decide),
    source_yRow_eq_rowCompute 11 9 9 4 (by decide),
    source_yRow_eq_rowCompute 11 9 9 5 (by decide),
    source_yRow_eq_rowCompute 11 9 9 6 (by decide),
    computeRow_11_9_9_0, computeRow_11_9_9_1, computeRow_11_9_9_2, computeRow_11_9_9_3, computeRow_11_9_9_4, computeRow_11_9_9_5, computeRow_11_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_9_11 : Y 11 9 11 = (390621018140645815377261/1048576000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 9 11 0 (by decide),
    source_yRow_eq_rowCompute 11 9 11 1 (by decide),
    source_yRow_eq_rowCompute 11 9 11 2 (by decide),
    source_yRow_eq_rowCompute 11 9 11 3 (by decide),
    source_yRow_eq_rowCompute 11 9 11 4 (by decide),
    source_yRow_eq_rowCompute 11 9 11 5 (by decide),
    source_yRow_eq_rowCompute 11 9 11 6 (by decide),
    computeRow_11_9_11_0, computeRow_11_9_11_1, computeRow_11_9_11_2, computeRow_11_9_11_3, computeRow_11_9_11_4, computeRow_11_9_11_5, computeRow_11_9_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_11_11_11 : Y 11 11 11 = (-7434351034101698173344801/524288000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 11 11 11 0 (by decide),
    source_yRow_eq_rowCompute 11 11 11 1 (by decide),
    source_yRow_eq_rowCompute 11 11 11 2 (by decide),
    source_yRow_eq_rowCompute 11 11 11 3 (by decide),
    source_yRow_eq_rowCompute 11 11 11 4 (by decide),
    source_yRow_eq_rowCompute 11 11 11 5 (by decide),
    source_yRow_eq_rowCompute 11 11 11 6 (by decide),
    computeRow_11_11_11_0, computeRow_11_11_11_1, computeRow_11_11_11_2, computeRow_11_11_11_3, computeRow_11_11_11_4, computeRow_11_11_11_5, computeRow_11_11_11_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_11_1_1 : Z 11 1 1 = (7257600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_1

theorem source_gram_11_1_3 : Z 11 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_3

theorem source_gram_11_1_5 : Z 11 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_5

theorem source_gram_11_1_7 : Z 11 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_7

theorem source_gram_11_1_9 : Z 11 1 9 = (-453600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_9

theorem source_gram_11_1_11 : Z 11 1 11 = (9979200 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_1_11

theorem source_gram_11_3_3 : Z 11 3 3 = (241920 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_3

theorem source_gram_11_3_5 : Z 11 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_5

theorem source_gram_11_3_7 : Z 11 3 7 = (-60480 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_7

theorem source_gram_11_3_9 : Z 11 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_9

theorem source_gram_11_3_11 : Z 11 3 11 = (2494800 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_3_11

theorem source_gram_11_5_5 : Z 11 5 5 = (54000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_5

theorem source_gram_11_5_7 : Z 11 5 7 = (-75600 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_7

theorem source_gram_11_5_9 : Z 11 5 9 = (113400 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_9

theorem source_gram_11_5_11 : Z 11 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_5_11

theorem source_gram_11_7_7 : Z 11 7 7 = (120960 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_7

theorem source_gram_11_7_9 : Z 11 7 9 = (-158760 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_9

theorem source_gram_11_7_11 : Z 11 7 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_7_11

theorem source_gram_11_9_9 : Z 11 9 9 = (266490 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_9

theorem source_gram_11_9_11 : Z 11 9 11 = (-623700 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_9_11

theorem source_gram_11_11_11 : Z 11 11 11 = (39449025 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_11_11_11

theorem source_error_11_3_1 : Y 11 3 1 = (-21091981152473935416162441/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_3

theorem source_gram_11_3_1 : Z 11 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_3

theorem source_error_11_5_1 : Y 11 5 1 = (1759644912412486678804947/134217728000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_5

theorem source_gram_11_5_1 : Z 11 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_5

theorem source_error_11_5_3 : Y 11 5 3 = (-110846050581407277067047/13421772800000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_5

theorem source_gram_11_5_3 : Z 11 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_5

theorem source_error_11_7_1 : Y 11 7 1 = (-7117902998608090523107887/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_7

theorem source_gram_11_7_1 : Z 11 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_7

theorem source_error_11_7_3 : Y 11 7 3 = (-120000452149124136234801/167772160000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_7

theorem source_gram_11_7_3 : Z 11 7 3 = (-60480 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_7

theorem source_error_11_7_5 : Y 11 7 5 = (-132022995280028243088831/67108864000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_7

theorem source_gram_11_7_5 : Z 11 7 5 = (-75600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_7

theorem source_error_11_9_1 : Y 11 9 1 = (2050140304557578762479287/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_9

theorem source_gram_11_9_1 : Z 11 9 1 = (-453600 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_9

theorem source_error_11_9_3 : Y 11 9 3 = (-804905973848069092119267/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_9

theorem source_gram_11_9_3 : Z 11 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_9

theorem source_error_11_9_5 : Y 11 9 5 = (39011604836809336804287/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_9

theorem source_gram_11_9_5 : Z 11 9 5 = (113400 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_9

theorem source_error_11_9_7 : Y 11 9 7 = (581826960578730870868149/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_7_9

theorem source_gram_11_9_7 : Z 11 9 7 = (-158760 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_9

theorem source_error_11_11_1 : Y 11 11 1 = (-3816671070411211699962099/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_1_11

theorem source_gram_11_11_1 : Z 11 11 1 = (9979200 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_1_11

theorem source_error_11_11_3 : Y 11 11 3 = (-488664944191263381981813/20971520000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_3_11

theorem source_gram_11_11_3 : Z 11 11 3 = (2494800 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_3_11

theorem source_error_11_11_5 : Y 11 11 5 = (-536635508982633719381547/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_5_11

theorem source_gram_11_11_5 : Z 11 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_5_11

theorem source_error_11_11_7 : Y 11 11 7 = (48169578758531066711919/20971520000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_7_11

theorem source_gram_11_11_7 : Z 11 11 7 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_7_11

theorem source_error_11_11_9 : Y 11 11 9 = (390621018140645815377261/1048576000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_11_9_11

theorem source_gram_11_11_9 : Z 11 11 9 = (-623700 : ℚ) := by
  rw [Z_symm]
  exact source_gram_11_9_11

theorem error_11 : errorRational 11 = candidateY_11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_11_1_1
  · exact source_error_11_1_3
  · exact source_error_11_1_5
  · exact source_error_11_1_7
  · exact source_error_11_1_9
  · exact source_error_11_1_11
  · exact source_error_11_3_1
  · exact source_error_11_3_3
  · exact source_error_11_3_5
  · exact source_error_11_3_7
  · exact source_error_11_3_9
  · exact source_error_11_3_11
  · exact source_error_11_5_1
  · exact source_error_11_5_3
  · exact source_error_11_5_5
  · exact source_error_11_5_7
  · exact source_error_11_5_9
  · exact source_error_11_5_11
  · exact source_error_11_7_1
  · exact source_error_11_7_3
  · exact source_error_11_7_5
  · exact source_error_11_7_7
  · exact source_error_11_7_9
  · exact source_error_11_7_11
  · exact source_error_11_9_1
  · exact source_error_11_9_3
  · exact source_error_11_9_5
  · exact source_error_11_9_7
  · exact source_error_11_9_9
  · exact source_error_11_9_11
  · exact source_error_11_11_1
  · exact source_error_11_11_3
  · exact source_error_11_11_5
  · exact source_error_11_11_7
  · exact source_error_11_11_9
  · exact source_error_11_11_11

theorem gram_11 : gramRational 11 = candidateZ_11 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_11_1_1
  · exact source_gram_11_1_3
  · exact source_gram_11_1_5
  · exact source_gram_11_1_7
  · exact source_gram_11_1_9
  · exact source_gram_11_1_11
  · exact source_gram_11_3_1
  · exact source_gram_11_3_3
  · exact source_gram_11_3_5
  · exact source_gram_11_3_7
  · exact source_gram_11_3_9
  · exact source_gram_11_3_11
  · exact source_gram_11_5_1
  · exact source_gram_11_5_3
  · exact source_gram_11_5_5
  · exact source_gram_11_5_7
  · exact source_gram_11_5_9
  · exact source_gram_11_5_11
  · exact source_gram_11_7_1
  · exact source_gram_11_7_3
  · exact source_gram_11_7_5
  · exact source_gram_11_7_7
  · exact source_gram_11_7_9
  · exact source_gram_11_7_11
  · exact source_gram_11_9_1
  · exact source_gram_11_9_3
  · exact source_gram_11_9_5
  · exact source_gram_11_9_7
  · exact source_gram_11_9_9
  · exact source_gram_11_9_11
  · exact source_gram_11_11_1
  · exact source_gram_11_11_3
  · exact source_gram_11_11_5
  · exact source_gram_11_11_7
  · exact source_gram_11_11_9
  · exact source_gram_11_11_11

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_11 : MatrixCompute.compressed 11 candidateY_11 candidateZ_11 =
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
  · exact computeLDL_11_5_5

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive11
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_11 : compressedRational 11 =
    lower_11 * Matrix.diagonal pivots_11 * lower_11.transpose := by
  rw [compressedRational_eq_compute, error_11, gram_11]
  exact candidateLDL_11

theorem four_body_11_positive_oai :
    ((compressedRational 11).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_11 pivots_11 ldl_11
  intro i
  fin_cases i <;> norm_num [pivots_11]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_11_positive_oai := @OAI.Laughlin.Certificate.four_body_11_positive_oai
