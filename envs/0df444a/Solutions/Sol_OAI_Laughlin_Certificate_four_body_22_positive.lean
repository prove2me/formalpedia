-- Prove2me | solution 1 for OAI.Laughlin.Certificate.four_body_22_positive
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T09:28:55.947418+00:00
-- url     : https://prove2.me/submissions/1a1bf92d-f38e-448d-bacc-a9b99cf306a1

import Mathlib
import Definitions.Def_OAIQ047L000
import Theorems.Thm_OAI_Laughlin_Certificate_error_22

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeQuadruples22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeQuadruples_22 : GramCompute.quadruples 22 = [(0,1,2,20), (0,1,3,19), (0,1,4,18), (0,1,5,17), (0,1,6,16), (0,1,7,15), (0,1,8,14), (0,1,9,13), (0,1,10,12), (0,2,3,18), (0,2,4,17), (0,2,5,16), (0,2,6,15), (0,2,7,14), (0,2,8,13), (0,2,9,12), (0,2,10,11), (0,3,4,16), (0,3,5,15), (0,3,6,14), (0,3,7,13), (0,3,8,12), (0,3,9,11), (0,4,5,14), (0,4,6,13), (0,4,7,12), (0,4,8,11), (0,4,9,10), (0,5,6,12), (0,5,7,11), (0,5,8,10), (0,6,7,10), (0,6,8,9), (1,2,3,17), (1,2,4,16), (1,2,5,15), (1,2,6,14), (1,2,7,13), (1,2,8,12), (1,2,9,11), (1,3,4,15), (1,3,5,14), (1,3,6,13), (1,3,7,12), (1,3,8,11), (1,3,9,10), (1,4,5,13), (1,4,6,12), (1,4,7,11), (1,4,8,10), (1,5,6,11), (1,5,7,10), (1,5,8,9), (1,6,7,9), (2,3,4,14), (2,3,5,13), (2,3,6,12), (2,3,7,11), (2,3,8,10), (2,4,5,12), (2,4,6,11), (2,4,7,10), (2,4,8,9), (2,5,6,10), (2,5,7,9), (2,6,7,8), (3,4,5,11), (3,4,6,10), (3,4,7,9), (3,5,6,9), (3,5,7,8), (4,5,6,8)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram01Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_1_1 : GramCompute.ZFast 22 1 1 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_3 : GramCompute.ZFast 22 1 3 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_5 : GramCompute.ZFast 22 1 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_7 : GramCompute.ZFast 22 1 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_9 : GramCompute.ZFast 22 1 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_11 : GramCompute.ZFast 22 1 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_13 : GramCompute.ZFast 22 1 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_15 : GramCompute.ZFast 22 1 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_17 : GramCompute.ZFast 22 1 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_19 : GramCompute.ZFast 22 1 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_1_21 : GramCompute.ZFast 22 1 21 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram03Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_3_3 : GramCompute.ZFast 22 3 3 = (729870602452992000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_5 : GramCompute.ZFast 22 3 5 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_7 : GramCompute.ZFast 22 3 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_9 : GramCompute.ZFast 22 3 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_11 : GramCompute.ZFast 22 3 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_13 : GramCompute.ZFast 22 3 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_15 : GramCompute.ZFast 22 3 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_17 : GramCompute.ZFast 22 3 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_19 : GramCompute.ZFast 22 3 19 = (-25659513367488000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_3_21 : GramCompute.ZFast 22 3 21 = (798295971432960000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram05Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_5_5 : GramCompute.ZFast 22 5 5 = (42682491371520000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_7 : GramCompute.ZFast 22 5 7 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_9 : GramCompute.ZFast 22 5 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_11 : GramCompute.ZFast 22 5 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_13 : GramCompute.ZFast 22 5 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_15 : GramCompute.ZFast 22 5 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_17 : GramCompute.ZFast 22 5 17 = (-2667655710720000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_19 : GramCompute.ZFast 22 5 19 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_5_21 : GramCompute.ZFast 22 5 21 = (598721978574720000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram07Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_7_7 : GramCompute.ZFast 22 7 7 = (6590678814720000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_9 : GramCompute.ZFast 22 7 9 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_11 : GramCompute.ZFast 22 7 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_13 : GramCompute.ZFast 22 7 13 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_15 : GramCompute.ZFast 22 7 15 = (-540641621520000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_17 : GramCompute.ZFast 22 7 17 = (-3501298120320000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_19 : GramCompute.ZFast 22 7 19 = (24946749107280000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_7_21 : GramCompute.ZFast 22 7 21 = (299360989287360000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram09Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_9_9 : GramCompute.ZFast 22 9 9 = (2259661307904000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_11 : GramCompute.ZFast 22 9 11 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_13 : GramCompute.ZFast 22 9 13 = (-211843247616000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_15 : GramCompute.ZFast 22 9 15 = (-1544690347200000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_17 : GramCompute.ZFast 22 9 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_19 : GramCompute.ZFast 22 9 19 = (25659513367488000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_9_21 : GramCompute.ZFast 22 9 21 = (99786996429120000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram11Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_11_11 : GramCompute.ZFast 22 11 11 = (1437750246240000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_11_13 : GramCompute.ZFast 22 11 13 = (-970948218240000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_11_15 : GramCompute.ZFast 22 11 15 = (-1274369536440000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_11_17 : GramCompute.ZFast 22 11 17 = (2751019951680000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_11_19 : GramCompute.ZFast 22 11 19 = (9800508577860000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_11_21 : GramCompute.ZFast 22 11 21 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram13Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_13_13 : GramCompute.ZFast 22 13 13 = (997428624192000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_13_15 : GramCompute.ZFast 22 13 15 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_13_17 : GramCompute.ZFast 22 13 17 = (0 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_13_19 : GramCompute.ZFast 22 13 19 = (-9265935382704000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_13_21 : GramCompute.ZFast 22 13 21 = (-37420123660920000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram15Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_15_15 : GramCompute.ZFast 22 15 15 = (5440206316545000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_17 : GramCompute.ZFast 22 15 17 = (-8534414168280000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_19 : GramCompute.ZFast 22 15 19 = (-23387577288075000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_15_21 : GramCompute.ZFast 22 15 21 = (-43656810937740000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram17Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_17_17 : GramCompute.ZFast 22 17 17 = (22841802023040000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_17_19 : GramCompute.ZFast 22 17 19 = (-30292481058840000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_17_21 : GramCompute.ZFast 22 17 21 = (-37420123660920000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram19Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_19_19 : GramCompute.ZFast 22 19 19 = (698765124659852250 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

theorem computeGram_22_19_21 : GramCompute.ZFast 22 19 21 = (-28065092745690000 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeGram212122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeGram_22_21_21 : GramCompute.ZFast 22 21 21 = (51071452523969377500 : ℚ) := by
  unfold GramCompute.ZFast
  rw [computeQuadruples_22]
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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL00Batch22
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

theorem computeLDL_22_0_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 0 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 0 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL01Batch22
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

theorem computeLDL_22_1_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 1 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 1 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL02Batch22
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

theorem computeLDL_22_2_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_2_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 2 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 2 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL03Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_3_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_3_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 3 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 3 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL04Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_4_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_4_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 4 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 4 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL05Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_5_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_5_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 5 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 5 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL06Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_6_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_6_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 6 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 6 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL07Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_7_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_7_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 7 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 7 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL08Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_8_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_8_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 8 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 8 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL09Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_9_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_9_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 9 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 9 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_ComputeLDL10Batch22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem computeLDL_22_10_0 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 0 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 0 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_1 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 1 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 1 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_2 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 2 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 2 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_3 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 3 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 3 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_4 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 4 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 4 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_5 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 5 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 5 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_6 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 6 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 6 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_7 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 7 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 7 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_8 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 8 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 8 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_9 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 9 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 9 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

theorem computeLDL_22_10_10 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 10 10 =
    (lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose) 10 10 := by
  rw [MatrixCompute.compressed_apply, MatrixCompute.ldl_apply]
  decide +kernel

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

theorem L_eq_fast (D r : ℕ) (A : ℕ × ℕ × ℕ × ℕ) : L D r A = LFast D r A := by
  simp only [L, LFast, V_eq_fast]

theorem Z_eq_fast (D r s : ℕ) : Z D r s = ZFast D r s := by
  simp only [Z, ZFast, L_eq_fast]

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
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_GramData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem source_gram_22_1_1 : Z 22 1 1 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_1

theorem source_gram_22_1_3 : Z 22 1 3 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_3

theorem source_gram_22_1_5 : Z 22 1 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_5

theorem source_gram_22_1_7 : Z 22 1 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_7

theorem source_gram_22_1_9 : Z 22 1 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_9

theorem source_gram_22_1_11 : Z 22 1 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_11

theorem source_gram_22_1_13 : Z 22 1 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_13

theorem source_gram_22_1_15 : Z 22 1 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_15

theorem source_gram_22_1_17 : Z 22 1 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_17

theorem source_gram_22_1_19 : Z 22 1 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_19

theorem source_gram_22_1_21 : Z 22 1 21 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_1_21

theorem source_gram_22_3_3 : Z 22 3 3 = (729870602452992000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_3

theorem source_gram_22_3_5 : Z 22 3 5 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_5

theorem source_gram_22_3_7 : Z 22 3 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_7

theorem source_gram_22_3_9 : Z 22 3 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_9

theorem source_gram_22_3_11 : Z 22 3 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_11

theorem source_gram_22_3_13 : Z 22 3 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_13

theorem source_gram_22_3_15 : Z 22 3 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_15

theorem source_gram_22_3_17 : Z 22 3 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_17

theorem source_gram_22_3_19 : Z 22 3 19 = (-25659513367488000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_19

theorem source_gram_22_3_21 : Z 22 3 21 = (798295971432960000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_3_21

theorem source_gram_22_5_5 : Z 22 5 5 = (42682491371520000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_5

theorem source_gram_22_5_7 : Z 22 5 7 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_7

theorem source_gram_22_5_9 : Z 22 5 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_9

theorem source_gram_22_5_11 : Z 22 5 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_11

theorem source_gram_22_5_13 : Z 22 5 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_13

theorem source_gram_22_5_15 : Z 22 5 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_15

theorem source_gram_22_5_17 : Z 22 5 17 = (-2667655710720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_17

theorem source_gram_22_5_19 : Z 22 5 19 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_19

theorem source_gram_22_5_21 : Z 22 5 21 = (598721978574720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_5_21

theorem source_gram_22_7_7 : Z 22 7 7 = (6590678814720000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_7

theorem source_gram_22_7_9 : Z 22 7 9 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_9

theorem source_gram_22_7_11 : Z 22 7 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_11

theorem source_gram_22_7_13 : Z 22 7 13 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_13

theorem source_gram_22_7_15 : Z 22 7 15 = (-540641621520000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_15

theorem source_gram_22_7_17 : Z 22 7 17 = (-3501298120320000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_17

theorem source_gram_22_7_19 : Z 22 7 19 = (24946749107280000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_19

theorem source_gram_22_7_21 : Z 22 7 21 = (299360989287360000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_7_21

theorem source_gram_22_9_9 : Z 22 9 9 = (2259661307904000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_9

theorem source_gram_22_9_11 : Z 22 9 11 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_11

theorem source_gram_22_9_13 : Z 22 9 13 = (-211843247616000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_13

theorem source_gram_22_9_15 : Z 22 9 15 = (-1544690347200000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_15

theorem source_gram_22_9_17 : Z 22 9 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_17

theorem source_gram_22_9_19 : Z 22 9 19 = (25659513367488000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_19

theorem source_gram_22_9_21 : Z 22 9 21 = (99786996429120000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_9_21

theorem source_gram_22_11_11 : Z 22 11 11 = (1437750246240000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_11

theorem source_gram_22_11_13 : Z 22 11 13 = (-970948218240000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_13

theorem source_gram_22_11_15 : Z 22 11 15 = (-1274369536440000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_15

theorem source_gram_22_11_17 : Z 22 11 17 = (2751019951680000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_17

theorem source_gram_22_11_19 : Z 22 11 19 = (9800508577860000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_19

theorem source_gram_22_11_21 : Z 22 11 21 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_11_21

theorem source_gram_22_13_13 : Z 22 13 13 = (997428624192000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_13_13

theorem source_gram_22_13_15 : Z 22 13 15 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_13_15

theorem source_gram_22_13_17 : Z 22 13 17 = (0 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_13_17

theorem source_gram_22_13_19 : Z 22 13 19 = (-9265935382704000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_13_19

theorem source_gram_22_13_21 : Z 22 13 21 = (-37420123660920000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_13_21

theorem source_gram_22_15_15 : Z 22 15 15 = (5440206316545000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_15_15

theorem source_gram_22_15_17 : Z 22 15 17 = (-8534414168280000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_15_17

theorem source_gram_22_15_19 : Z 22 15 19 = (-23387577288075000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_15_19

theorem source_gram_22_15_21 : Z 22 15 21 = (-43656810937740000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_15_21

theorem source_gram_22_17_17 : Z 22 17 17 = (22841802023040000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_17_17

theorem source_gram_22_17_19 : Z 22 17 19 = (-30292481058840000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_17_19

theorem source_gram_22_17_21 : Z 22 17 21 = (-37420123660920000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_17_21

theorem source_gram_22_19_19 : Z 22 19 19 = (698765124659852250 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_19_19

theorem source_gram_22_19_21 : Z 22 19 21 = (-28065092745690000 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_19_21

theorem source_gram_22_21_21 : Z 22 21 21 = (51071452523969377500 : ℚ) := by
  rw [Z_eq_gramCompute]
  exact computeGram_22_21_21

theorem source_gram_22_3_1 : Z 22 3 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_3

theorem source_gram_22_5_1 : Z 22 5 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_5

theorem source_gram_22_5_3 : Z 22 5 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_5

theorem source_gram_22_7_1 : Z 22 7 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_7

theorem source_gram_22_7_3 : Z 22 7 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_7

theorem source_gram_22_7_5 : Z 22 7 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_7

theorem source_gram_22_9_1 : Z 22 9 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_9

theorem source_gram_22_9_3 : Z 22 9 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_9

theorem source_gram_22_9_5 : Z 22 9 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_9

theorem source_gram_22_9_7 : Z 22 9 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_9

theorem source_gram_22_11_1 : Z 22 11 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_11

theorem source_gram_22_11_3 : Z 22 11 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_11

theorem source_gram_22_11_5 : Z 22 11 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_11

theorem source_gram_22_11_7 : Z 22 11 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_11

theorem source_gram_22_11_9 : Z 22 11 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_11

theorem source_gram_22_13_1 : Z 22 13 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_13

theorem source_gram_22_13_3 : Z 22 13 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_13

theorem source_gram_22_13_5 : Z 22 13 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_13

theorem source_gram_22_13_7 : Z 22 13 7 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_13

theorem source_gram_22_13_9 : Z 22 13 9 = (-211843247616000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_13

theorem source_gram_22_13_11 : Z 22 13 11 = (-970948218240000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_11_13

theorem source_gram_22_15_1 : Z 22 15 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_15

theorem source_gram_22_15_3 : Z 22 15 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_15

theorem source_gram_22_15_5 : Z 22 15 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_15

theorem source_gram_22_15_7 : Z 22 15 7 = (-540641621520000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_15

theorem source_gram_22_15_9 : Z 22 15 9 = (-1544690347200000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_15

theorem source_gram_22_15_11 : Z 22 15 11 = (-1274369536440000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_11_15

theorem source_gram_22_15_13 : Z 22 15 13 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_13_15

theorem source_gram_22_17_1 : Z 22 17 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_17

theorem source_gram_22_17_3 : Z 22 17 3 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_17

theorem source_gram_22_17_5 : Z 22 17 5 = (-2667655710720000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_17

theorem source_gram_22_17_7 : Z 22 17 7 = (-3501298120320000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_17

theorem source_gram_22_17_9 : Z 22 17 9 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_17

theorem source_gram_22_17_11 : Z 22 17 11 = (2751019951680000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_11_17

theorem source_gram_22_17_13 : Z 22 17 13 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_13_17

theorem source_gram_22_17_15 : Z 22 17 15 = (-8534414168280000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_15_17

theorem source_gram_22_19_1 : Z 22 19 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_19

theorem source_gram_22_19_3 : Z 22 19 3 = (-25659513367488000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_19

theorem source_gram_22_19_5 : Z 22 19 5 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_19

theorem source_gram_22_19_7 : Z 22 19 7 = (24946749107280000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_19

theorem source_gram_22_19_9 : Z 22 19 9 = (25659513367488000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_19

theorem source_gram_22_19_11 : Z 22 19 11 = (9800508577860000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_11_19

theorem source_gram_22_19_13 : Z 22 19 13 = (-9265935382704000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_13_19

theorem source_gram_22_19_15 : Z 22 19 15 = (-23387577288075000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_15_19

theorem source_gram_22_19_17 : Z 22 19 17 = (-30292481058840000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_17_19

theorem source_gram_22_21_1 : Z 22 21 1 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_1_21

theorem source_gram_22_21_3 : Z 22 21 3 = (798295971432960000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_3_21

theorem source_gram_22_21_5 : Z 22 21 5 = (598721978574720000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_5_21

theorem source_gram_22_21_7 : Z 22 21 7 = (299360989287360000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_7_21

theorem source_gram_22_21_9 : Z 22 21 9 = (99786996429120000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_9_21

theorem source_gram_22_21_11 : Z 22 21 11 = (0 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_11_21

theorem source_gram_22_21_13 : Z 22 21 13 = (-37420123660920000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_13_21

theorem source_gram_22_21_15 : Z 22 21 15 = (-43656810937740000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_15_21

theorem source_gram_22_21_17 : Z 22 21 17 = (-37420123660920000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_17_21

theorem source_gram_22_21_19 : Z 22 21 19 = (-28065092745690000 : ℚ) := by
  rw [Z_symm]
  exact source_gram_22_19_21

theorem gram_22 : gramRational 22 = candidateZ_22 := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact source_gram_22_1_1
  · exact source_gram_22_1_3
  · exact source_gram_22_1_5
  · exact source_gram_22_1_7
  · exact source_gram_22_1_9
  · exact source_gram_22_1_11
  · exact source_gram_22_1_13
  · exact source_gram_22_1_15
  · exact source_gram_22_1_17
  · exact source_gram_22_1_19
  · exact source_gram_22_1_21
  · exact source_gram_22_3_1
  · exact source_gram_22_3_3
  · exact source_gram_22_3_5
  · exact source_gram_22_3_7
  · exact source_gram_22_3_9
  · exact source_gram_22_3_11
  · exact source_gram_22_3_13
  · exact source_gram_22_3_15
  · exact source_gram_22_3_17
  · exact source_gram_22_3_19
  · exact source_gram_22_3_21
  · exact source_gram_22_5_1
  · exact source_gram_22_5_3
  · exact source_gram_22_5_5
  · exact source_gram_22_5_7
  · exact source_gram_22_5_9
  · exact source_gram_22_5_11
  · exact source_gram_22_5_13
  · exact source_gram_22_5_15
  · exact source_gram_22_5_17
  · exact source_gram_22_5_19
  · exact source_gram_22_5_21
  · exact source_gram_22_7_1
  · exact source_gram_22_7_3
  · exact source_gram_22_7_5
  · exact source_gram_22_7_7
  · exact source_gram_22_7_9
  · exact source_gram_22_7_11
  · exact source_gram_22_7_13
  · exact source_gram_22_7_15
  · exact source_gram_22_7_17
  · exact source_gram_22_7_19
  · exact source_gram_22_7_21
  · exact source_gram_22_9_1
  · exact source_gram_22_9_3
  · exact source_gram_22_9_5
  · exact source_gram_22_9_7
  · exact source_gram_22_9_9
  · exact source_gram_22_9_11
  · exact source_gram_22_9_13
  · exact source_gram_22_9_15
  · exact source_gram_22_9_17
  · exact source_gram_22_9_19
  · exact source_gram_22_9_21
  · exact source_gram_22_11_1
  · exact source_gram_22_11_3
  · exact source_gram_22_11_5
  · exact source_gram_22_11_7
  · exact source_gram_22_11_9
  · exact source_gram_22_11_11
  · exact source_gram_22_11_13
  · exact source_gram_22_11_15
  · exact source_gram_22_11_17
  · exact source_gram_22_11_19
  · exact source_gram_22_11_21
  · exact source_gram_22_13_1
  · exact source_gram_22_13_3
  · exact source_gram_22_13_5
  · exact source_gram_22_13_7
  · exact source_gram_22_13_9
  · exact source_gram_22_13_11
  · exact source_gram_22_13_13
  · exact source_gram_22_13_15
  · exact source_gram_22_13_17
  · exact source_gram_22_13_19
  · exact source_gram_22_13_21
  · exact source_gram_22_15_1
  · exact source_gram_22_15_3
  · exact source_gram_22_15_5
  · exact source_gram_22_15_7
  · exact source_gram_22_15_9
  · exact source_gram_22_15_11
  · exact source_gram_22_15_13
  · exact source_gram_22_15_15
  · exact source_gram_22_15_17
  · exact source_gram_22_15_19
  · exact source_gram_22_15_21
  · exact source_gram_22_17_1
  · exact source_gram_22_17_3
  · exact source_gram_22_17_5
  · exact source_gram_22_17_7
  · exact source_gram_22_17_9
  · exact source_gram_22_17_11
  · exact source_gram_22_17_13
  · exact source_gram_22_17_15
  · exact source_gram_22_17_17
  · exact source_gram_22_17_19
  · exact source_gram_22_17_21
  · exact source_gram_22_19_1
  · exact source_gram_22_19_3
  · exact source_gram_22_19_5
  · exact source_gram_22_19_7
  · exact source_gram_22_19_9
  · exact source_gram_22_19_11
  · exact source_gram_22_19_13
  · exact source_gram_22_19_15
  · exact source_gram_22_19_17
  · exact source_gram_22_19_19
  · exact source_gram_22_19_21
  · exact source_gram_22_21_1
  · exact source_gram_22_21_3
  · exact source_gram_22_21_5
  · exact source_gram_22_21_7
  · exact source_gram_22_21_9
  · exact source_gram_22_21_11
  · exact source_gram_22_21_13
  · exact source_gram_22_21_15
  · exact source_gram_22_21_17
  · exact source_gram_22_21_19
  · exact source_gram_22_21_21

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_LDLData22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
theorem candidateLDL_22 : MatrixCompute.compressed 22 candidateY_22 candidateZ_22 =
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
  · exact computeLDL_22_0_10
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
  · exact computeLDL_22_1_10
  · exact computeLDL_22_2_0
  · exact computeLDL_22_2_1
  · exact computeLDL_22_2_2
  · exact computeLDL_22_2_3
  · exact computeLDL_22_2_4
  · exact computeLDL_22_2_5
  · exact computeLDL_22_2_6
  · exact computeLDL_22_2_7
  · exact computeLDL_22_2_8
  · exact computeLDL_22_2_9
  · exact computeLDL_22_2_10
  · exact computeLDL_22_3_0
  · exact computeLDL_22_3_1
  · exact computeLDL_22_3_2
  · exact computeLDL_22_3_3
  · exact computeLDL_22_3_4
  · exact computeLDL_22_3_5
  · exact computeLDL_22_3_6
  · exact computeLDL_22_3_7
  · exact computeLDL_22_3_8
  · exact computeLDL_22_3_9
  · exact computeLDL_22_3_10
  · exact computeLDL_22_4_0
  · exact computeLDL_22_4_1
  · exact computeLDL_22_4_2
  · exact computeLDL_22_4_3
  · exact computeLDL_22_4_4
  · exact computeLDL_22_4_5
  · exact computeLDL_22_4_6
  · exact computeLDL_22_4_7
  · exact computeLDL_22_4_8
  · exact computeLDL_22_4_9
  · exact computeLDL_22_4_10
  · exact computeLDL_22_5_0
  · exact computeLDL_22_5_1
  · exact computeLDL_22_5_2
  · exact computeLDL_22_5_3
  · exact computeLDL_22_5_4
  · exact computeLDL_22_5_5
  · exact computeLDL_22_5_6
  · exact computeLDL_22_5_7
  · exact computeLDL_22_5_8
  · exact computeLDL_22_5_9
  · exact computeLDL_22_5_10
  · exact computeLDL_22_6_0
  · exact computeLDL_22_6_1
  · exact computeLDL_22_6_2
  · exact computeLDL_22_6_3
  · exact computeLDL_22_6_4
  · exact computeLDL_22_6_5
  · exact computeLDL_22_6_6
  · exact computeLDL_22_6_7
  · exact computeLDL_22_6_8
  · exact computeLDL_22_6_9
  · exact computeLDL_22_6_10
  · exact computeLDL_22_7_0
  · exact computeLDL_22_7_1
  · exact computeLDL_22_7_2
  · exact computeLDL_22_7_3
  · exact computeLDL_22_7_4
  · exact computeLDL_22_7_5
  · exact computeLDL_22_7_6
  · exact computeLDL_22_7_7
  · exact computeLDL_22_7_8
  · exact computeLDL_22_7_9
  · exact computeLDL_22_7_10
  · exact computeLDL_22_8_0
  · exact computeLDL_22_8_1
  · exact computeLDL_22_8_2
  · exact computeLDL_22_8_3
  · exact computeLDL_22_8_4
  · exact computeLDL_22_8_5
  · exact computeLDL_22_8_6
  · exact computeLDL_22_8_7
  · exact computeLDL_22_8_8
  · exact computeLDL_22_8_9
  · exact computeLDL_22_8_10
  · exact computeLDL_22_9_0
  · exact computeLDL_22_9_1
  · exact computeLDL_22_9_2
  · exact computeLDL_22_9_3
  · exact computeLDL_22_9_4
  · exact computeLDL_22_9_5
  · exact computeLDL_22_9_6
  · exact computeLDL_22_9_7
  · exact computeLDL_22_9_8
  · exact computeLDL_22_9_9
  · exact computeLDL_22_9_10
  · exact computeLDL_22_10_0
  · exact computeLDL_22_10_1
  · exact computeLDL_22_10_2
  · exact computeLDL_22_10_3
  · exact computeLDL_22_10_4
  · exact computeLDL_22_10_5
  · exact computeLDL_22_10_6
  · exact computeLDL_22_10_7
  · exact computeLDL_22_10_8
  · exact computeLDL_22_10_9
  · exact computeLDL_22_10_10

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ047_LA.Laughlin_FiniteFlux_Positive22
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate

theorem ldl_22 : compressedRational 22 =
    lower_22 * Matrix.diagonal pivots_22 * lower_22.transpose := by
  rw [compressedRational_eq_compute, error_22, gram_22]
  exact candidateLDL_22

theorem four_body_22_positive_oai :
    ((compressedRational 22).map (Rat.castHom ℝ)).PosSemidef := by
  apply rational_ldl_positive _ lower_22 pivots_22 ldl_22
  intro i
  fin_cases i <;> norm_num [pivots_22]

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.four_body_22_positive_oai := @OAI.Laughlin.Certificate.four_body_22_positive_oai
