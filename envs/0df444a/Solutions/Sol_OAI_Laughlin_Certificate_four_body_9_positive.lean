-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_9_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T21:31:11.373794+00:00
-- url     : https://prove2.me/submissions/9dbfe863-11a8-495b-baa6-1d9e88051632

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_1_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_3_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_5_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeGram_9_7_7
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_0_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_0_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_1_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_2_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_2_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_3_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_3_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_4_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeLDL_9_4_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_1_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_1_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_1_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_1_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_3_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_3_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_5_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_7_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_9_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_3_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_5_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_5_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_5_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_7_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_7_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_7_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_9_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_5_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_7_7_2
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_7_7_4
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_7_9_0
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_7_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_7_9_5
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_9_9_1
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_9_9_3
import Theorems.Thm_OAI_Laughlin_Certificate_computeRow_9_9_9_6
import Theorems.Thm_OAI_Laughlin_Certificate_yRow_eq_integral

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_9 : GramCompute.quadruples 9 = [(0,1,2,7), (0,1,3,6), (0,1,4,5), (0,2,3,5), (1,2,3,4)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeGram_9_1_3 : GramCompute.ZFast 9 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_1_7 : GramCompute.ZFast 9 1 7 = (-10080 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_1_9 : GramCompute.ZFast 9 1 9 = (136080 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_3_5 : GramCompute.ZFast 9 3 5 = (-2160 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_3_9 : GramCompute.ZFast 9 3 9 = (22680 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_5_5 : GramCompute.ZFast 9 5 5 = (1080 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_5_9 : GramCompute.ZFast 9 5 9 = (-11340 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_7_9 : GramCompute.ZFast 9 7 9 = (-17010 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
  decide +kernel

theorem computeGram_9_9_9 : GramCompute.ZFast 9 9 9 = (348705 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_9]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeLDL_9_0_1 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 0 1 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 0 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_0_2 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 0 2 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 0 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_0_4 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 0 4 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 0 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_1_1 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 1 1 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 1 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_1_2 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 1 2 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 1 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_1_4 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 1 4 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 1 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_2_1 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 2 1 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_2_2 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 2 2 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_2_4 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 2 4 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_3_1 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 3 1 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_3_2 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 3 2 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_3_4 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 3 4 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_4_0 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 4 0 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_4_2 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 4 2 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_9_4_4 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 4 4 =
    (lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_1_1_0 : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[0]!) =
    (2270297435168965978403072601191383028383543508040941568000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_1_2 : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[2]!) =
    (41346031182378793781597609623152154759830386496031948800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_1_4 : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[4]!) =
    (-37553938374178000501861985259244278923855776310938828800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_1_5 : RowCompute.yRowIntegralFast 9 1 1 (RowCompute.rows[5]!) =
    (76235936847784777904537168736168341929959941525943091200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_0 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[0]!) =
    (-279062421380172067529857348024358190744997899746987212800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_1 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[1]!) =
    (-459360885322437236466125812039608637656853533960437760000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_3 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[3]!) =
    (14938515937034594999877003710229050926038061338014515200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_5 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[5]!) =
    (109393309605793398426247870349258171849606499573694464000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_3_6 : RowCompute.yRowIntegralFast 9 1 3 (RowCompute.rows[6]!) =
    (8721086357081805385975272257328250909745983137408614400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_1 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[1]!) =
    (336320165288866155966027442267636959269808379338424320000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_3 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[3]!) =
    (33886163539748383224392155439022704107458560405589196800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_4 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[4]!) =
    (16923800992130264548028553653580871266607186616883609600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_5_6 : RowCompute.yRowIntegralFast 9 1 5 (RowCompute.rows[6]!) =
    (-7806328388432177408073340623748203428941925474893824000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_7_1 : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[1]!) =
    (196201169909344198624037734613914413817876634130186240000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_7_2 : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[2]!) =
    (318497787373230022621846263417507616223978248732252569600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_7_4 : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[4]!) =
    (18350308771858577105307400623724226671522394569231564800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_7_5 : RowCompute.yRowIntegralFast 9 1 7 (RowCompute.rows[5]!) =
    (-159612221178564449766948711529885255742982854368926105600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_9_0 : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[0]!) =
    (1180610090631053483523386696083103292457630720668676915200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_9_2 : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[2]!) =
    (-1832584883711806352049783458905515161278143837422537932800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_9_3 : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[3]!) =
    (-2179319552316453496586166470077264078299743172366119731200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_1_9_5 : RowCompute.yRowIntegralFast 9 1 9 (RowCompute.rows[5]!) =
    (6174537322347062432314509559542073526390628249973555200000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow092
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_3_3_0 : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[0]!) =
    (-43821115925842203320053988125351069936558183162262323200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_3_1 : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[1]!) =
    (331915542829280497752118299464899080321970808637358080000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_3_3 : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[3]!) =
    (62025373133485546819008012173368125888982268480009011200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_3_5 : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[5]!) =
    (-45667609193662076397581128711286400674402287739102822400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_3_6 : RowCompute.yRowIntegralFast 9 3 3 (RowCompute.rows[6]!) =
    (-10884436241201625231978184416380859700696821654355968000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_1 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[1]!) =
    (-251721159274289624971784653147597378347202310528040960000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_2 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[2]!) =
    (30856573776962976395503016709439403238848723287434854400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_4 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[4]!) =
    (1840739597139051079457637812474924906987764596709785600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_5_6 : RowCompute.yRowIntegralFast 9 3 5 (RowCompute.rows[6]!) =
    (-46346496825727039607863683025836935535518947265740800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_7_0 : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[0]!) =
    (544703131953073817992423779320315083589387418569225011200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_7_2 : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[2]!) =
    (-230237947671548553434773588186996985634647710316573491200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_7_4 : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[4]!) =
    (-37607597714567809541866072770068715465170583394713600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_7_5 : RowCompute.yRowIntegralFast 9 3 7 (RowCompute.rows[5]!) =
    (100188512236944272455080366533948709017444524655168716800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_9_0 : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[0]!) =
    (-365161574167416125525714440335106171066612774979449651200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_9_1 : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[1]!) =
    (473724369918531900154924050478803009539441479448002560000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_9_3 : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[3]!) =
    (1406453421493163243211986024745972339268084692350612275200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_9_5 : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[5]!) =
    (-79903268440648484280054072467915626844599141384008499200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_3_9_6 : RowCompute.yRowIntegralFast 9 3 9 (RowCompute.rows[6]!) =
    (1073937509183672217155063116822763692295103153438720000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_5_1 : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[1]!) =
    (119300599438911812640226045736813021644856900053893120000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_5_3 : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[3]!) =
    (22371361631886006452686625443849798873724402393520537600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_5_4 : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[4]!) =
    (-2072025228373979156003408557207519816095968493620428800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_5_6 : RowCompute.yRowIntegralFast 9 5 5 (RowCompute.rows[6]!) =
    (-2202918812580164038884917147458813550448296762907033600000 : ℤ) := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeRow093
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem computeRow_9_5_7_1 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[1]!) =
    (-511362978859533248104163501739314364391697144988303360000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_2 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[2]!) =
    (-138626485543771537044192482926094436237431707100459827200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_4 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[4]!) =
    (1152950035722211064982468230212159927150714408874803200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_7_5 : RowCompute.yRowIntegralFast 9 5 7 (RowCompute.rows[5]!) =
    (-20888681307310678226735427883924546231730943832778342400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_9_0 : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[0]!) =
    (-1393574231809287581637586994306240930954451752334026342400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_9_2 : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[2]!) =
    (347053641700695650218250237803173902667117160495998566400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_9_3 : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[3]!) =
    (-1282606096375737849288017328668732768645543054349120307200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_5_9_5 : RowCompute.yRowIntegralFast 9 5 9 (RowCompute.rows[5]!) =
    (64328727028239207084667190361482670467827808505692160000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_0 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[0]!) =
    (1730299036951487279704336142420470070729823124691563315200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_1 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[1]!) =
    (-302627006093845813559800606047016673864445229919109120000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_3 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[3]!) =
    (48023594568254777314005298943874196381302147438870528000000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_5 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[5]!) =
    (84700007125431340587265300729828955859716934862268006400000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_7_6 : RowCompute.yRowIntegralFast 9 7 7 (RowCompute.rows[6]!) =
    (-16443967375424498629864692499661996754210893446565068800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_9_1 : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[1]!) =
    (-164722870900864384691326021978198948564096273078026240000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_9_2 : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[2]!) =
    (-1508637311404667824213454472817530894067875215318817177600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_9_4 : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[4]!) =
    (282415214225792176601491484220438168812021482013904076800000 : ℤ) := by
  decide +kernel

theorem computeRow_9_7_9_6 : RowCompute.yRowIntegralFast 9 7 9 (RowCompute.rows[6]!) =
    (-9237093472369599179193613792151538787648783472866099200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_9_9_0 : RowCompute.yRowIntegralFast 9 9 9 (RowCompute.rows[0]!) =
    (28133001505392295960878803268377382855959448189958461849600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_9_9_2 : RowCompute.yRowIntegralFast 9 9 9 (RowCompute.rows[2]!) =
    (41719956091676531783489814387969300622030468899042597273600000 : ℤ) := by
  decide +kernel

theorem computeRow_9_9_9_4 : RowCompute.yRowIntegralFast 9 9 9 (RowCompute.rows[4]!) =
    (2790477382083186194437827438125590714024946750410928947200000 : ℤ) := by
  decide +kernel

theorem computeRow_9_9_9_5 : RowCompute.yRowIntegralFast 9 9 9 (RowCompute.rows[5]!) =
    (-323815667508707914437523935534172580723534987517335961600000 : ℤ) := by
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem source_error_9_1_1 : Y 9 1 1 = (-12465910883340844333323483/6710886400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 1 0 (by decide),
    source_yRow_eq_rowCompute 9 1 1 1 (by decide),
    source_yRow_eq_rowCompute 9 1 1 2 (by decide),
    source_yRow_eq_rowCompute 9 1 1 3 (by decide),
    source_yRow_eq_rowCompute 9 1 1 4 (by decide),
    source_yRow_eq_rowCompute 9 1 1 5 (by decide),
    source_yRow_eq_rowCompute 9 1 1 6 (by decide),
    computeRow_9_1_1_0, computeRow_9_1_1_1, computeRow_9_1_1_2, computeRow_9_1_1_3, computeRow_9_1_1_4, computeRow_9_1_1_5, computeRow_9_1_1_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_3 : Y 9 1 3 = (-33961811903853786055197/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 3 0 (by decide),
    source_yRow_eq_rowCompute 9 1 3 1 (by decide),
    source_yRow_eq_rowCompute 9 1 3 2 (by decide),
    source_yRow_eq_rowCompute 9 1 3 3 (by decide),
    source_yRow_eq_rowCompute 9 1 3 4 (by decide),
    source_yRow_eq_rowCompute 9 1 3 5 (by decide),
    source_yRow_eq_rowCompute 9 1 3 6 (by decide),
    computeRow_9_1_3_0, computeRow_9_1_3_1, computeRow_9_1_3_2, computeRow_9_1_3_3, computeRow_9_1_3_4, computeRow_9_1_3_5, computeRow_9_1_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_5 : Y 9 1 5 = (-670994343426034247927913/6710886400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 5 0 (by decide),
    source_yRow_eq_rowCompute 9 1 5 1 (by decide),
    source_yRow_eq_rowCompute 9 1 5 2 (by decide),
    source_yRow_eq_rowCompute 9 1 5 3 (by decide),
    source_yRow_eq_rowCompute 9 1 5 4 (by decide),
    source_yRow_eq_rowCompute 9 1 5 5 (by decide),
    source_yRow_eq_rowCompute 9 1 5 6 (by decide),
    computeRow_9_1_5_0, computeRow_9_1_5_1, computeRow_9_1_5_2, computeRow_9_1_5_3, computeRow_9_1_5_4, computeRow_9_1_5_5, computeRow_9_1_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_7 : Y 9 1 7 = (4530779263986412498504797/3355443200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 7 0 (by decide),
    source_yRow_eq_rowCompute 9 1 7 1 (by decide),
    source_yRow_eq_rowCompute 9 1 7 2 (by decide),
    source_yRow_eq_rowCompute 9 1 7 3 (by decide),
    source_yRow_eq_rowCompute 9 1 7 4 (by decide),
    source_yRow_eq_rowCompute 9 1 7 5 (by decide),
    source_yRow_eq_rowCompute 9 1 7 6 (by decide),
    computeRow_9_1_7_0, computeRow_9_1_7_1, computeRow_9_1_7_2, computeRow_9_1_7_3, computeRow_9_1_7_4, computeRow_9_1_7_5, computeRow_9_1_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_1_9 : Y 9 1 9 = (2064320406503781558919011/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 1 9 0 (by decide),
    source_yRow_eq_rowCompute 9 1 9 1 (by decide),
    source_yRow_eq_rowCompute 9 1 9 2 (by decide),
    source_yRow_eq_rowCompute 9 1 9 3 (by decide),
    source_yRow_eq_rowCompute 9 1 9 4 (by decide),
    source_yRow_eq_rowCompute 9 1 9 5 (by decide),
    source_yRow_eq_rowCompute 9 1 9 6 (by decide),
    computeRow_9_1_9_0, computeRow_9_1_9_1, computeRow_9_1_9_2, computeRow_9_1_9_3, computeRow_9_1_9_4, computeRow_9_1_9_5, computeRow_9_1_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_3 : Y 9 3 3 = (2960534512700301116069433/23488102400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 3 0 (by decide),
    source_yRow_eq_rowCompute 9 3 3 1 (by decide),
    source_yRow_eq_rowCompute 9 3 3 2 (by decide),
    source_yRow_eq_rowCompute 9 3 3 3 (by decide),
    source_yRow_eq_rowCompute 9 3 3 4 (by decide),
    source_yRow_eq_rowCompute 9 3 3 5 (by decide),
    source_yRow_eq_rowCompute 9 3 3 6 (by decide),
    computeRow_9_3_3_0, computeRow_9_3_3_1, computeRow_9_3_3_2, computeRow_9_3_3_3, computeRow_9_3_3_4, computeRow_9_3_3_5, computeRow_9_3_3_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_5 : Y 9 3 5 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 5 0 (by decide),
    source_yRow_eq_rowCompute 9 3 5 1 (by decide),
    source_yRow_eq_rowCompute 9 3 5 2 (by decide),
    source_yRow_eq_rowCompute 9 3 5 3 (by decide),
    source_yRow_eq_rowCompute 9 3 5 4 (by decide),
    source_yRow_eq_rowCompute 9 3 5 5 (by decide),
    source_yRow_eq_rowCompute 9 3 5 6 (by decide),
    computeRow_9_3_5_0, computeRow_9_3_5_1, computeRow_9_3_5_2, computeRow_9_3_5_3, computeRow_9_3_5_4, computeRow_9_3_5_5, computeRow_9_3_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_7 : Y 9 3 7 = (-172612848420190308157317/419430400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 7 0 (by decide),
    source_yRow_eq_rowCompute 9 3 7 1 (by decide),
    source_yRow_eq_rowCompute 9 3 7 2 (by decide),
    source_yRow_eq_rowCompute 9 3 7 3 (by decide),
    source_yRow_eq_rowCompute 9 3 7 4 (by decide),
    source_yRow_eq_rowCompute 9 3 7 5 (by decide),
    source_yRow_eq_rowCompute 9 3 7 6 (by decide),
    computeRow_9_3_7_0, computeRow_9_3_7_1, computeRow_9_3_7_2, computeRow_9_3_7_3, computeRow_9_3_7_4, computeRow_9_3_7_5, computeRow_9_3_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_3_9 : Y 9 3 9 = (-460639144770506834240727/209715200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 3 9 0 (by decide),
    source_yRow_eq_rowCompute 9 3 9 1 (by decide),
    source_yRow_eq_rowCompute 9 3 9 2 (by decide),
    source_yRow_eq_rowCompute 9 3 9 3 (by decide),
    source_yRow_eq_rowCompute 9 3 9 4 (by decide),
    source_yRow_eq_rowCompute 9 3 9 5 (by decide),
    source_yRow_eq_rowCompute 9 3 9 6 (by decide),
    computeRow_9_3_9_0, computeRow_9_3_9_1, computeRow_9_3_9_2, computeRow_9_3_9_3, computeRow_9_3_9_4, computeRow_9_3_9_5, computeRow_9_3_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_5 : Y 9 5 5 = (-12391755266391716879263611/46976204800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 5 0 (by decide),
    source_yRow_eq_rowCompute 9 5 5 1 (by decide),
    source_yRow_eq_rowCompute 9 5 5 2 (by decide),
    source_yRow_eq_rowCompute 9 5 5 3 (by decide),
    source_yRow_eq_rowCompute 9 5 5 4 (by decide),
    source_yRow_eq_rowCompute 9 5 5 5 (by decide),
    source_yRow_eq_rowCompute 9 5 5 6 (by decide),
    computeRow_9_5_5_0, computeRow_9_5_5_1, computeRow_9_5_5_2, computeRow_9_5_5_3, computeRow_9_5_5_4, computeRow_9_5_5_5, computeRow_9_5_5_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_7 : Y 9 5 7 = (202846259663372040293217/3355443200000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 7 0 (by decide),
    source_yRow_eq_rowCompute 9 5 7 1 (by decide),
    source_yRow_eq_rowCompute 9 5 7 2 (by decide),
    source_yRow_eq_rowCompute 9 5 7 3 (by decide),
    source_yRow_eq_rowCompute 9 5 7 4 (by decide),
    source_yRow_eq_rowCompute 9 5 7 5 (by decide),
    source_yRow_eq_rowCompute 9 5 7 6 (by decide),
    computeRow_9_5_7_0, computeRow_9_5_7_1, computeRow_9_5_7_2, computeRow_9_5_7_3, computeRow_9_5_7_4, computeRow_9_5_7_5, computeRow_9_5_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_5_9 : Y 9 5 9 = (1717697222431419971099331/838860800000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 5 9 0 (by decide),
    source_yRow_eq_rowCompute 9 5 9 1 (by decide),
    source_yRow_eq_rowCompute 9 5 9 2 (by decide),
    source_yRow_eq_rowCompute 9 5 9 3 (by decide),
    source_yRow_eq_rowCompute 9 5 9 4 (by decide),
    source_yRow_eq_rowCompute 9 5 9 5 (by decide),
    source_yRow_eq_rowCompute 9 5 9 6 (by decide),
    computeRow_9_5_9_0, computeRow_9_5_9_1, computeRow_9_5_9_2, computeRow_9_5_9_3, computeRow_9_5_9_4, computeRow_9_5_9_5, computeRow_9_5_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_7_7 : Y 9 7 7 = (-3138981013037239731556773/1677721600000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 7 7 0 (by decide),
    source_yRow_eq_rowCompute 9 7 7 1 (by decide),
    source_yRow_eq_rowCompute 9 7 7 2 (by decide),
    source_yRow_eq_rowCompute 9 7 7 3 (by decide),
    source_yRow_eq_rowCompute 9 7 7 4 (by decide),
    source_yRow_eq_rowCompute 9 7 7 5 (by decide),
    source_yRow_eq_rowCompute 9 7 7 6 (by decide),
    computeRow_9_7_7_0, computeRow_9_7_7_1, computeRow_9_7_7_2, computeRow_9_7_7_3, computeRow_9_7_7_4, computeRow_9_7_7_5, computeRow_9_7_7_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_7_9 : Y 9 7 9 = (-1034085603218724160418079/419430400000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 7 9 0 (by decide),
    source_yRow_eq_rowCompute 9 7 9 1 (by decide),
    source_yRow_eq_rowCompute 9 7 9 2 (by decide),
    source_yRow_eq_rowCompute 9 7 9 3 (by decide),
    source_yRow_eq_rowCompute 9 7 9 4 (by decide),
    source_yRow_eq_rowCompute 9 7 9 5 (by decide),
    source_yRow_eq_rowCompute 9 7 9 6 (by decide),
    computeRow_9_7_9_0, computeRow_9_7_9_1, computeRow_9_7_9_2, computeRow_9_7_9_3, computeRow_9_7_9_4, computeRow_9_7_9_5, computeRow_9_7_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_error_9_9_9 : Y 9 9 9 = (-9956547203160990435022917/104857600000000000000 : ℚ) := by
  rw [Y_expand, source_yRow_eq_rowCompute 9 9 9 0 (by decide),
    source_yRow_eq_rowCompute 9 9 9 1 (by decide),
    source_yRow_eq_rowCompute 9 9 9 2 (by decide),
    source_yRow_eq_rowCompute 9 9 9 3 (by decide),
    source_yRow_eq_rowCompute 9 9 9 4 (by decide),
    source_yRow_eq_rowCompute 9 9 9 5 (by decide),
    source_yRow_eq_rowCompute 9 9 9 6 (by decide),
    computeRow_9_9_9_0, computeRow_9_9_9_1, computeRow_9_9_9_2, computeRow_9_9_9_3, computeRow_9_9_9_4, computeRow_9_9_9_5, computeRow_9_9_9_6]
  norm_num [arithmeticScale, Nat.factorial]

theorem source_gram_9_1_1 : Z 9 1 1 = (80640 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_1

theorem source_gram_9_1_3 : Z 9 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_3

theorem source_gram_9_1_5 : Z 9 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_5

theorem source_gram_9_1_7 : Z 9 1 7 = (-10080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_7

theorem source_gram_9_1_9 : Z 9 1 9 = (136080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_1_9

theorem source_gram_9_3_3 : Z 9 3 3 = (4320 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_3

theorem source_gram_9_3_5 : Z 9 3 5 = (-2160 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_5

theorem source_gram_9_3_7 : Z 9 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_7

theorem source_gram_9_3_9 : Z 9 3 9 = (22680 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_3_9

theorem source_gram_9_5_5 : Z 9 5 5 = (1080 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_5

theorem source_gram_9_5_7 : Z 9 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_7

theorem source_gram_9_5_9 : Z 9 5 9 = (-11340 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_5_9

theorem source_gram_9_7_7 : Z 9 7 7 = (1260 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_7_7

theorem source_gram_9_7_9 : Z 9 7 9 = (-17010 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_7_9

theorem source_gram_9_9_9 : Z 9 9 9 = (348705 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_9_9_9

theorem source_error_9_3_1 : Y 9 3 1 = (-33961811903853786055197/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_3

theorem source_gram_9_3_1 : Z 9 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_3

theorem source_error_9_5_1 : Y 9 5 1 = (-670994343426034247927913/6710886400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_5

theorem source_gram_9_5_1 : Z 9 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_5

theorem source_error_9_5_3 : Y 9 5 3 = (-249132079557021880785303/11744051200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_5

theorem source_gram_9_5_3 : Z 9 5 3 = (-2160 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_5

theorem source_error_9_7_1 : Y 9 7 1 = (4530779263986412498504797/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_7

theorem source_gram_9_7_1 : Z 9 7 1 = (-10080 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_7

theorem source_error_9_7_3 : Y 9 7 3 = (-172612848420190308157317/419430400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_7

theorem source_gram_9_7_3 : Z 9 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_7

theorem source_error_9_7_5 : Y 9 7 5 = (202846259663372040293217/3355443200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_5_7

theorem source_gram_9_7_5 : Z 9 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_5_7

theorem source_error_9_9_1 : Y 9 9 1 = (2064320406503781558919011/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_1_9

theorem source_gram_9_9_1 : Z 9 9 1 = (136080 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_1_9

theorem source_error_9_9_3 : Y 9 9 3 = (-460639144770506834240727/209715200000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_3_9

theorem source_gram_9_9_3 : Z 9 9 3 = (22680 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_3_9

theorem source_error_9_9_5 : Y 9 9 5 = (1717697222431419971099331/838860800000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_5_9

theorem source_gram_9_9_5 : Z 9 9 5 = (-11340 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_5_9

theorem source_error_9_9_7 : Y 9 9 7 = (-1034085603218724160418079/419430400000000000000 : ℚ) := by
  rw [Y_symm]
  exact source_error_9_7_9

theorem source_gram_9_9_7 : Z 9 9 7 = (-17010 : ℚ) := by
  rw [Z_symm]
  exact source_gram_9_7_9

theorem error_9 : errorRational 9 = candidateY_9 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_error_9_1_1
  · exact source_error_9_1_3
  · exact source_error_9_1_5
  · exact source_error_9_1_7
  · exact source_error_9_1_9
  · exact source_error_9_3_1
  · exact source_error_9_3_3
  · exact source_error_9_3_5
  · exact source_error_9_3_7
  · exact source_error_9_3_9
  · exact source_error_9_5_1
  · exact source_error_9_5_3
  · exact source_error_9_5_5
  · exact source_error_9_5_7
  · exact source_error_9_5_9
  · exact source_error_9_7_1
  · exact source_error_9_7_3
  · exact source_error_9_7_5
  · exact source_error_9_7_7
  · exact source_error_9_7_9
  · exact source_error_9_9_1
  · exact source_error_9_9_3
  · exact source_error_9_9_5
  · exact source_error_9_9_7
  · exact source_error_9_9_9

theorem gram_9 : gramRational 9 = candidateZ_9 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_9_1_1
  · exact source_gram_9_1_3
  · exact source_gram_9_1_5
  · exact source_gram_9_1_7
  · exact source_gram_9_1_9
  · exact source_gram_9_3_1
  · exact source_gram_9_3_3
  · exact source_gram_9_3_5
  · exact source_gram_9_3_7
  · exact source_gram_9_3_9
  · exact source_gram_9_5_1
  · exact source_gram_9_5_3
  · exact source_gram_9_5_5
  · exact source_gram_9_5_7
  · exact source_gram_9_5_9
  · exact source_gram_9_7_1
  · exact source_gram_9_7_3
  · exact source_gram_9_7_5
  · exact source_gram_9_7_7
  · exact source_gram_9_7_9
  · exact source_gram_9_9_1
  · exact source_gram_9_9_3
  · exact source_gram_9_9_5
  · exact source_gram_9_9_7
  · exact source_gram_9_9_9

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_9 : MatrixCompute.compressed 9 candidateY_9 candidateZ_9 =
    lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact computeLDL_9_0_0
  · exact computeLDL_9_0_1
  · exact computeLDL_9_0_2
  · exact computeLDL_9_0_3
  · exact computeLDL_9_0_4
  · exact computeLDL_9_1_0
  · exact computeLDL_9_1_1
  · exact computeLDL_9_1_2
  · exact computeLDL_9_1_3
  · exact computeLDL_9_1_4
  · exact computeLDL_9_2_0
  · exact computeLDL_9_2_1
  · exact computeLDL_9_2_2
  · exact computeLDL_9_2_3
  · exact computeLDL_9_2_4
  · exact computeLDL_9_3_0
  · exact computeLDL_9_3_1
  · exact computeLDL_9_3_2
  · exact computeLDL_9_3_3
  · exact computeLDL_9_3_4
  · exact computeLDL_9_4_0
  · exact computeLDL_9_4_1
  · exact computeLDL_9_4_2
  · exact computeLDL_9_4_3
  · exact computeLDL_9_4_4

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_9 : compressedRational 9 =
    lower_9 * Matrix.diagonal pivots_9 * lower_9.transpose := by
  rw [compressedRational_eq_compute, error_9, gram_9]
  exact candidateLDL_9

theorem four_body_9_positive_oai :
    ((compressedRational 9).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_9 pivots_9 ldl_9
  intro i
  fin_cases i <;> norm_num [pivots_9]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_9_positive_oai := @OAI.Laughlin.Certificate.four_body_9_positive_oai
