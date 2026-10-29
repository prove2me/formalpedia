-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_10_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:30:47.976286+00:00
-- url     : https://prove2.me/submissions/66d111f3-7aeb-4d11-a0b5-d0d13a310f74

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_3_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_5_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_10_7_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_0_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_0_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_2_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_2_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_4_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_10_4_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_1_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_3_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_5_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_7_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_7_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_7_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_7_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_7_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_9_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_9_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_10_9_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_eq_integral

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_10 : GramCompute.quadruples 10 = [(0,1,2,8), (0,1,3,7), (0,1,4,6), (0,2,3,6), (0,2,4,5), (1,2,3,5)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_10_1_3 : GramCompute.ZFast 10 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_7 : GramCompute.ZFast 10 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_1_9 : GramCompute.ZFast 10 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_5 : GramCompute.ZFast 10 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_3_9 : GramCompute.ZFast 10 3 9 = (90720 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_5_5 : GramCompute.ZFast 10 5 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_5_9 : GramCompute.ZFast 10 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_7_9 : GramCompute.ZFast 10 7 9 = (-68040 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
  decide +kernel

theorem computeGram_10_9_9 : GramCompute.ZFast 10 9 9 = (272160 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_10]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeLDL_10_0_1 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 1 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_0_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 0 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 0 4 := by
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

theorem computeLDL_10_1_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 1 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 1 4 := by
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

theorem computeLDL_10_2_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 2 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 2 4 := by
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

theorem computeLDL_10_3_4 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 3 4 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_0 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 0 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_10_4_2 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 4 2 =
    (lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose) 4 2 := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_1_1_0 : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[0]!) =
    (-11893289179714257419266005071504248621945711650584238489600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_1_2 : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[2]!) =
    (-5377168696689471907961950336652473735387859585006881996800000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_1_4 : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[4]!) =
    (217152235481090690469952868694571699250134770866611814400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_1_5 : RowCompute.yRowIntegralFast 10 1 1 (RowCompute.rows[5]!) =
    (-6180819132862231576077330610139911077499333971959768678400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_3_0 : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[0]!) =
    (1179481577503315176048684874875584303760921381646526054400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_3_1 : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[1]!) =
    (3808580079510807494525154505240713601525223965222502400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_3_3 : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[3]!) =
    (3174378540690214028515344677157200059548804260560896000000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_3_5 : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[5]!) =
    (779445443057431724243852853685752120258652309668495360000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_3_6 : RowCompute.yRowIntegralFast 10 1 3 (RowCompute.rows[6]!) =
    (127409654331645329346642758441524269306809355148984320000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_5_1 : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[1]!) =
    (-1400549610778725049523448138835398758304389447811072000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_5_3 : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[3]!) =
    (-1810144540684055650798881836580682534472933370702594048000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_5_4 : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[4]!) =
    (-68894137166280209965983323882682877754536132136140800000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_5_6 : RowCompute.yRowIntegralFast 10 1 5 (RowCompute.rows[6]!) =
    (-35912325448799105030647324761071512574945709042696192000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_7_1 : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[1]!) =
    (6961368902067217870814701128129671531436543954439372800000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_7_2 : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[2]!) =
    (3355947006278983502579592582432628605355585983260865331200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_7_4 : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[4]!) =
    (-177365567883273131227503767679961232590004790443271782400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_7_5 : RowCompute.yRowIntegralFast 10 1 7 (RowCompute.rows[5]!) =
    (1218779542424888373371772368873817728220987002198163456000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_9_0 : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[0]!) =
    (-18883051498201713570799320688213219529961738359191633920000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_9_2 : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[2]!) =
    (-8364088924931162512567336469542673394839339944046179123200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_9_3 : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[3]!) =
    (-3816408206406626250234956053493938010700668624658707251200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_1_9_5 : RowCompute.yRowIntegralFast 10 1 9 (RowCompute.rows[5]!) =
    (3625424627867909123836967880731844845396499568459461427200000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_3_3_0 : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[0]!) =
    (375436119532883651035692137601181650560056611134295244800000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_3_1 : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[1]!) =
    (-419819387803002322044839157944723965725653255533363200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_3_3 : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[3]!) =
    (-837135394266418075492252231435681113586931728714511155200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_3_5 : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[5]!) =
    (3411632341474926049557095268483256268306550665458483200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_3_6 : RowCompute.yRowIntegralFast 10 3 3 (RowCompute.rows[6]!) =
    (-62484212688761792192672009220482890123267689891967795200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_5_1 : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[1]!) =
    (190681242273948569158418475500825533837809102618624000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_5_2 : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[2]!) =
    (711137955871359072309613005090566697873018462991810560000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_5_4 : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[4]!) =
    (7211448379848369230177589829073891407084995502669824000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_5_6 : RowCompute.yRowIntegralFast 10 3 5 (RowCompute.rows[6]!) =
    (5122288052030436543112161768849174808266983470006272000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_7_0 : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[0]!) =
    (-2208762636442268389950670498806278954419976822664147763200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_7_2 : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[2]!) =
    (-715842274998526829808134019427994118122029992807864729600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_7_4 : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[4]!) =
    (-110266585485114533503099962138991369701616789803447091200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_7_5 : RowCompute.yRowIntegralFast 10 3 7 (RowCompute.rows[5]!) =
    (-341531742405753704617453573085791441872329866856733081600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_9_0 : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[0]!) =
    (5792405095051787807484698078694423683381245810742761881600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_9_1 : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[1]!) =
    (2775941348849472436558648094468460567775938303806668800000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_9_3 : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[3]!) =
    (2118394098482944012529122497811890335834954953454203699200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_9_5 : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[5]!) =
    (-404004917259812106555340280976097636446287266107831091200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_3_9_6 : RowCompute.yRowIntegralFast 10 3 9 (RowCompute.rows[6]!) =
    (-10623636481214188839067906124532038422102790127589785600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_5_1 : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[1]!) =
    (678156022562674724241112373412351312416796737273856000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_5_3 : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[3]!) =
    (-108608729814070839880752450425428824096095602200281088000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_5_4 : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[4]!) =
    (34358072693769491514009803627620980486475066028064768000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_5_6 : RowCompute.yRowIntegralFast 10 5 5 (RowCompute.rows[6]!) =
    (-14958717958597473469750646293503041560246381292027904000000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow103
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_10_5_7_1 : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[1]!) =
    (710338515902074020583843274623359396787089504731136000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_7_2 : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[2]!) =
    (580375085627931402664502362371822022827658257817927680000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_7_4 : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[4]!) =
    (-24590825319318657985152669249215334102538812691316736000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_7_5 : RowCompute.yRowIntegralFast 10 5 7 (RowCompute.rows[5]!) =
    (310934676282294843181586937263810699605073744917168128000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_9_0 : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[0]!) =
    (-7376583842805127430471734688403564193107872479709233152000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_9_2 : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[2]!) =
    (-1484907229245992372015043624647412210000002165728346112000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_9_3 : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[3]!) =
    (-17199249919663483374617759645775171641681374680711168000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_5_9_5 : RowCompute.yRowIntegralFast 10 5 9 (RowCompute.rows[5]!) =
    (4270672586824111352756423634450427650297276244426752000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_7_0 : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[0]!) =
    (-1565224641506481085939307345222295241233445340357591040000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_7_1 : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[1]!) =
    (-2346196907250935251703714689304055499523844953918668800000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_7_3 : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[3]!) =
    (438128184781406037849499305410387075605161987247020441600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_7_5 : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[5]!) =
    (36307483639854856814075107153596069215927712322525593600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_7_6 : RowCompute.yRowIntegralFast 10 7 7 (RowCompute.rows[6]!) =
    (-41156619219015220215450114403043755162670884202741760000000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_9_1 : RowCompute.yRowIntegralFast 10 7 9 (RowCompute.rows[1]!) =
    (5061182410295079092141470249082224477856351262238310400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_9_2 : RowCompute.yRowIntegralFast 10 7 9 (RowCompute.rows[2]!) =
    (-5397731808984013046007200505006226680699017090056165785600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_9_4 : RowCompute.yRowIntegralFast 10 7 9 (RowCompute.rows[4]!) =
    (-2603106245495435387191772822988723364257543560468889600000 : ℤ) := by
  decide +kernel

theorem computeRow_10_7_9_6 : RowCompute.yRowIntegralFast 10 7 9 (RowCompute.rows[6]!) =
    (-51807454905930158699348634146266062763348390773679718400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_9_9_0 : RowCompute.yRowIntegralFast 10 9 9 (RowCompute.rows[0]!) =
    (34430013513693262528433393724574481953319968932071945011200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_9_9_2 : RowCompute.yRowIntegralFast 10 9 9 (RowCompute.rows[2]!) =
    (39134717243797548676369576191286676738386912806666711859200000 : ℤ) := by
  decide +kernel

theorem computeRow_10_9_9_4 : RowCompute.yRowIntegralFast 10 9 9 (RowCompute.rows[4]!) =
    (1602990922447017680309118590783763041291244860982322790400000 : ℤ) := by
  decide +kernel

theorem computeRow_10_9_9_5 : RowCompute.yRowIntegralFast 10 9 9 (RowCompute.rows[5]!) =
    (-498476359915657649328937964716159040437828607105040384000000 : ℤ) := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_10_1_1 : Y 10 1 1 = (3252603773208384966897801/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 1 0 (by decide),
    source_yRow_eq_rowCompute 10 1 1 1 (by decide),
    source_yRow_eq_rowCompute 10 1 1 2 (by decide),
    source_yRow_eq_rowCompute 10 1 1 3 (by decide),
    source_yRow_eq_rowCompute 10 1 1 4 (by decide),
    source_yRow_eq_rowCompute 10 1 1 5 (by decide),
    source_yRow_eq_rowCompute 10 1 1 6 (by decide),
    computeRow_10_1_1_0, computeRow_10_1_1_1, computeRow_10_1_1_2, computeRow_10_1_1_3, computeRow_10_1_1_4, computeRow_10_1_1_5, computeRow_10_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_3 : Y 10 1 3 = (-1219963203744052188572919/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 3 0 (by decide),
    source_yRow_eq_rowCompute 10 1 3 1 (by decide),
    source_yRow_eq_rowCompute 10 1 3 2 (by decide),
    source_yRow_eq_rowCompute 10 1 3 3 (by decide),
    source_yRow_eq_rowCompute 10 1 3 4 (by decide),
    source_yRow_eq_rowCompute 10 1 3 5 (by decide),
    source_yRow_eq_rowCompute 10 1 3 6 (by decide),
    computeRow_10_1_3_0, computeRow_10_1_3_1, computeRow_10_1_3_2, computeRow_10_1_3_3, computeRow_10_1_3_4, computeRow_10_1_3_5, computeRow_10_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_5 : Y 10 1 5 = (1233781148459940320874483/134217728000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 5 0 (by decide),
    source_yRow_eq_rowCompute 10 1 5 1 (by decide),
    source_yRow_eq_rowCompute 10 1 5 2 (by decide),
    source_yRow_eq_rowCompute 10 1 5 3 (by decide),
    source_yRow_eq_rowCompute 10 1 5 4 (by decide),
    source_yRow_eq_rowCompute 10 1 5 5 (by decide),
    source_yRow_eq_rowCompute 10 1 5 6 (by decide),
    computeRow_10_1_5_0, computeRow_10_1_5_1, computeRow_10_1_5_2, computeRow_10_1_5_3, computeRow_10_1_5_4, computeRow_10_1_5_5, computeRow_10_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_7 : Y 10 1 7 = (-4673143458544379455879083/335544320000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 7 0 (by decide),
    source_yRow_eq_rowCompute 10 1 7 1 (by decide),
    source_yRow_eq_rowCompute 10 1 7 2 (by decide),
    source_yRow_eq_rowCompute 10 1 7 3 (by decide),
    source_yRow_eq_rowCompute 10 1 7 4 (by decide),
    source_yRow_eq_rowCompute 10 1 7 5 (by decide),
    source_yRow_eq_rowCompute 10 1 7 6 (by decide),
    computeRow_10_1_7_0, computeRow_10_1_7_1, computeRow_10_1_7_2, computeRow_10_1_7_3, computeRow_10_1_7_4, computeRow_10_1_7_5, computeRow_10_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_1_9 : Y 10 1 9 = (2012606963507139814961019/83886080000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 1 9 0 (by decide),
    source_yRow_eq_rowCompute 10 1 9 1 (by decide),
    source_yRow_eq_rowCompute 10 1 9 2 (by decide),
    source_yRow_eq_rowCompute 10 1 9 3 (by decide),
    source_yRow_eq_rowCompute 10 1 9 4 (by decide),
    source_yRow_eq_rowCompute 10 1 9 5 (by decide),
    source_yRow_eq_rowCompute 10 1 9 6 (by decide),
    computeRow_10_1_9_0, computeRow_10_1_9_1, computeRow_10_1_9_2, computeRow_10_1_9_3, computeRow_10_1_9_4, computeRow_10_1_9_5, computeRow_10_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_3 : Y 10 3 3 = (23917264894764854794377/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 3 0 (by decide),
    source_yRow_eq_rowCompute 10 3 3 1 (by decide),
    source_yRow_eq_rowCompute 10 3 3 2 (by decide),
    source_yRow_eq_rowCompute 10 3 3 3 (by decide),
    source_yRow_eq_rowCompute 10 3 3 4 (by decide),
    source_yRow_eq_rowCompute 10 3 3 5 (by decide),
    source_yRow_eq_rowCompute 10 3 3 6 (by decide),
    computeRow_10_3_3_0, computeRow_10_3_3_1, computeRow_10_3_3_2, computeRow_10_3_3_3, computeRow_10_3_3_4, computeRow_10_3_3_5, computeRow_10_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_5 : Y 10 3 5 = (-13854999171694482915831/8388608000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 5 0 (by decide),
    source_yRow_eq_rowCompute 10 3 5 1 (by decide),
    source_yRow_eq_rowCompute 10 3 5 2 (by decide),
    source_yRow_eq_rowCompute 10 3 5 3 (by decide),
    source_yRow_eq_rowCompute 10 3 5 4 (by decide),
    source_yRow_eq_rowCompute 10 3 5 5 (by decide),
    source_yRow_eq_rowCompute 10 3 5 6 (by decide),
    computeRow_10_3_5_0, computeRow_10_3_5_1, computeRow_10_3_5_2, computeRow_10_3_5_3, computeRow_10_3_5_4, computeRow_10_3_5_5, computeRow_10_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_7 : Y 10 3 7 = (57805337880323795919969/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 7 0 (by decide),
    source_yRow_eq_rowCompute 10 3 7 1 (by decide),
    source_yRow_eq_rowCompute 10 3 7 2 (by decide),
    source_yRow_eq_rowCompute 10 3 7 3 (by decide),
    source_yRow_eq_rowCompute 10 3 7 4 (by decide),
    source_yRow_eq_rowCompute 10 3 7 5 (by decide),
    source_yRow_eq_rowCompute 10 3 7 6 (by decide),
    computeRow_10_3_7_0, computeRow_10_3_7_1, computeRow_10_3_7_2, computeRow_10_3_7_3, computeRow_10_3_7_4, computeRow_10_3_7_5, computeRow_10_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_3_9 : Y 10 3 9 = (-52562004903703102850037/5242880000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 3 9 0 (by decide),
    source_yRow_eq_rowCompute 10 3 9 1 (by decide),
    source_yRow_eq_rowCompute 10 3 9 2 (by decide),
    source_yRow_eq_rowCompute 10 3 9 3 (by decide),
    source_yRow_eq_rowCompute 10 3 9 4 (by decide),
    source_yRow_eq_rowCompute 10 3 9 5 (by decide),
    source_yRow_eq_rowCompute 10 3 9 6 (by decide),
    computeRow_10_3_9_0, computeRow_10_3_9_1, computeRow_10_3_9_2, computeRow_10_3_9_3, computeRow_10_3_9_4, computeRow_10_3_9_5, computeRow_10_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_5 : Y 10 5 5 = (2285267576183515842978393/939524096000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 5 0 (by decide),
    source_yRow_eq_rowCompute 10 5 5 1 (by decide),
    source_yRow_eq_rowCompute 10 5 5 2 (by decide),
    source_yRow_eq_rowCompute 10 5 5 3 (by decide),
    source_yRow_eq_rowCompute 10 5 5 4 (by decide),
    source_yRow_eq_rowCompute 10 5 5 5 (by decide),
    source_yRow_eq_rowCompute 10 5 5 6 (by decide),
    computeRow_10_5_5_0, computeRow_10_5_5_1, computeRow_10_5_5_2, computeRow_10_5_5_3, computeRow_10_5_5_4, computeRow_10_5_5_5, computeRow_10_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_7 : Y 10 5 7 = (-121198635809384297528619/67108864000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 7 0 (by decide),
    source_yRow_eq_rowCompute 10 5 7 1 (by decide),
    source_yRow_eq_rowCompute 10 5 7 2 (by decide),
    source_yRow_eq_rowCompute 10 5 7 3 (by decide),
    source_yRow_eq_rowCompute 10 5 7 4 (by decide),
    source_yRow_eq_rowCompute 10 5 7 5 (by decide),
    source_yRow_eq_rowCompute 10 5 7 6 (by decide),
    computeRow_10_5_7_0, computeRow_10_5_7_1, computeRow_10_5_7_2, computeRow_10_5_7_3, computeRow_10_5_7_4, computeRow_10_5_7_5, computeRow_10_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_5_9 : Y 10 5 9 = (127922353790121014632767/16777216000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 5 9 0 (by decide),
    source_yRow_eq_rowCompute 10 5 9 1 (by decide),
    source_yRow_eq_rowCompute 10 5 9 2 (by decide),
    source_yRow_eq_rowCompute 10 5 9 3 (by decide),
    source_yRow_eq_rowCompute 10 5 9 4 (by decide),
    source_yRow_eq_rowCompute 10 5 9 5 (by decide),
    source_yRow_eq_rowCompute 10 5 9 6 (by decide),
    computeRow_10_5_9_0, computeRow_10_5_9_1, computeRow_10_5_9_2, computeRow_10_5_9_3, computeRow_10_5_9_4, computeRow_10_5_9_5, computeRow_10_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_7_7 : Y 10 7 7 = (51194502011873480782923/167772160000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 7 7 0 (by decide),
    source_yRow_eq_rowCompute 10 7 7 1 (by decide),
    source_yRow_eq_rowCompute 10 7 7 2 (by decide),
    source_yRow_eq_rowCompute 10 7 7 3 (by decide),
    source_yRow_eq_rowCompute 10 7 7 4 (by decide),
    source_yRow_eq_rowCompute 10 7 7 5 (by decide),
    source_yRow_eq_rowCompute 10 7 7 6 (by decide),
    computeRow_10_7_7_0, computeRow_10_7_7_1, computeRow_10_7_7_2, computeRow_10_7_7_3, computeRow_10_7_7_4, computeRow_10_7_7_5, computeRow_10_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_7_9 : Y 10 7 9 = (10203611212469228878953/41943040000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 7 9 0 (by decide),
    source_yRow_eq_rowCompute 10 7 9 1 (by decide),
    source_yRow_eq_rowCompute 10 7 9 2 (by decide),
    source_yRow_eq_rowCompute 10 7 9 3 (by decide),
    source_yRow_eq_rowCompute 10 7 9 4 (by decide),
    source_yRow_eq_rowCompute 10 7 9 5 (by decide),
    source_yRow_eq_rowCompute 10 7 9 6 (by decide),
    computeRow_10_7_9_0, computeRow_10_7_9_1, computeRow_10_7_9_2, computeRow_10_7_9_3, computeRow_10_7_9_4, computeRow_10_7_9_5, computeRow_10_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_10_9_9 : Y 10 9 9 = (-990036939147267786688413/10485760000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 10 9 9 0 (by decide),
    source_yRow_eq_rowCompute 10 9 9 1 (by decide),
    source_yRow_eq_rowCompute 10 9 9 2 (by decide),
    source_yRow_eq_rowCompute 10 9 9 3 (by decide),
    source_yRow_eq_rowCompute 10 9 9 4 (by decide),
    source_yRow_eq_rowCompute 10 9 9 5 (by decide),
    source_yRow_eq_rowCompute 10 9 9 6 (by decide),
    computeRow_10_9_9_0, computeRow_10_9_9_1, computeRow_10_9_9_2, computeRow_10_9_9_3, computeRow_10_9_9_4, computeRow_10_9_9_5, computeRow_10_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_10_1_1 : Z 10 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_1

theorem source_gram_10_1_3 : Z 10 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_3

theorem source_gram_10_1_5 : Z 10 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_5

theorem source_gram_10_1_7 : Z 10 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_7

theorem source_gram_10_1_9 : Z 10 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_1_9

theorem source_gram_10_3_3 : Z 10 3 3 = (30240 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_3

theorem source_gram_10_3_5 : Z 10 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_5

theorem source_gram_10_3_7 : Z 10 3 7 = (-22680 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_7

theorem source_gram_10_3_9 : Z 10 3 9 = (90720 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_3_9

theorem source_gram_10_5_5 : Z 10 5 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_5

theorem source_gram_10_5_7 : Z 10 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_7

theorem source_gram_10_5_9 : Z 10 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_5_9

theorem source_gram_10_7_7 : Z 10 7 7 = (17010 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_7

theorem source_gram_10_7_9 : Z 10 7 9 = (-68040 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_7_9

theorem source_gram_10_9_9 : Z 10 9 9 = (272160 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_10_9_9

theorem source_error_10_3_1 : Y 10 3 1 = (-1219963203744052188572919/167772160000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_3

theorem source_gram_10_3_1 : Z 10 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_3

theorem source_error_10_5_1 : Y 10 5 1 = (1233781148459940320874483/134217728000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_5

theorem source_gram_10_5_1 : Z 10 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_5

theorem source_error_10_5_3 : Y 10 5 3 = (-13854999171694482915831/8388608000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_5

theorem source_gram_10_5_3 : Z 10 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_5

theorem source_error_10_7_1 : Y 10 7 1 = (-4673143458544379455879083/335544320000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_7

theorem source_gram_10_7_1 : Z 10 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_7

theorem source_error_10_7_3 : Y 10 7 3 = (57805337880323795919969/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_7

theorem source_gram_10_7_3 : Z 10 7 3 = (-22680 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_7

theorem source_error_10_7_5 : Y 10 7 5 = (-121198635809384297528619/67108864000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_5_7

theorem source_gram_10_7_5 : Z 10 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_7

theorem source_error_10_9_1 : Y 10 9 1 = (2012606963507139814961019/83886080000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_1_9

theorem source_gram_10_9_1 : Z 10 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_1_9

theorem source_error_10_9_3 : Y 10 9 3 = (-52562004903703102850037/5242880000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_3_9

theorem source_gram_10_9_3 : Z 10 9 3 = (90720 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_3_9

theorem source_error_10_9_5 : Y 10 9 5 = (127922353790121014632767/16777216000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_5_9

theorem source_gram_10_9_5 : Z 10 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_5_9

theorem source_error_10_9_7 : Y 10 9 7 = (10203611212469228878953/41943040000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_10_7_9

theorem source_gram_10_9_7 : Z 10 9 7 = (-68040 : ℚ) := by
  rw [Z_symm]
  exact source_gram_10_7_9

theorem error_10 : errorRational 10 = candidateY_10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_10_1_1
  · exact source_error_10_1_3
  · exact source_error_10_1_5
  · exact source_error_10_1_7
  · exact source_error_10_1_9
  · exact source_error_10_3_1
  · exact source_error_10_3_3
  · exact source_error_10_3_5
  · exact source_error_10_3_7
  · exact source_error_10_3_9
  · exact source_error_10_5_1
  · exact source_error_10_5_3
  · exact source_error_10_5_5
  · exact source_error_10_5_7
  · exact source_error_10_5_9
  · exact source_error_10_7_1
  · exact source_error_10_7_3
  · exact source_error_10_7_5
  · exact source_error_10_7_7
  · exact source_error_10_7_9
  · exact source_error_10_9_1
  · exact source_error_10_9_3
  · exact source_error_10_9_5
  · exact source_error_10_9_7
  · exact source_error_10_9_9

theorem gram_10 : gramRational 10 = candidateZ_10 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_10_1_1
  · exact source_gram_10_1_3
  · exact source_gram_10_1_5
  · exact source_gram_10_1_7
  · exact source_gram_10_1_9
  · exact source_gram_10_3_1
  · exact source_gram_10_3_3
  · exact source_gram_10_3_5
  · exact source_gram_10_3_7
  · exact source_gram_10_3_9
  · exact source_gram_10_5_1
  · exact source_gram_10_5_3
  · exact source_gram_10_5_5
  · exact source_gram_10_5_7
  · exact source_gram_10_5_9
  · exact source_gram_10_7_1
  · exact source_gram_10_7_3
  · exact source_gram_10_7_5
  · exact source_gram_10_7_7
  · exact source_gram_10_7_9
  · exact source_gram_10_9_1
  · exact source_gram_10_9_3
  · exact source_gram_10_9_5
  · exact source_gram_10_9_7
  · exact source_gram_10_9_9

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_10 : MatrixCompute.compressed 10 candidateY_10 candidateZ_10 =
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

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive10
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_10 : compressedRational 10 =
    lower_10 * Matrix.diagonal pivots_10 * lower_10.transpose := by
  rw [compressedRational_eq_compute, error_10, gram_10]
  exact candidateLDL_10

theorem four_body_10_positive_oai :
    ((compressedRational 10).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_10 pivots_10 ldl_10
  intro i
  fin_cases i <;> norm_num [pivots_10]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_10_positive_oai := @OAI.Laughlin.Certificate.four_body_10_positive_oai
