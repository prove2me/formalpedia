-- Prove2me | solution 1 for OAI.Laughlin.Certificate.gram_8_s50
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-01T13:22:32.595192+00:00
-- url     : https://prove2.me/submissions/bf7bb6b0-db23-4ae6-b027-e82435192d02

import Mathlib
import Definitions.Def_OAIQ050L010

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Quadruples08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem quadruples_8 : quadruples 8 = [(0,1,2,6), (0,1,3,5), (0,2,3,4)] := by
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_FastChoose
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Gram082
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix

theorem gram_8_1_1 : Z 8 1 1 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_3 : Z 8 1 3 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_5 : Z 8 1 5 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_1_7 : Z 8 1 7 = (0 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_3 : Z 8 3 3 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_5 : Z 8 3 5 = (-720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_3_7 : Z 8 3 7 = (1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_5 : Z 8 5 5 = (720 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_5_7 : Z 8 5 7 = (-1260 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

theorem gram_8_7_7 : Z 8 7 7 = (2205 : ℚ) := by
  rw [Z_eq_fast]
  unfold ZFast
  rw [quadruples_8]
  decide +kernel

end Laughlin.Certificate

end OAI
end

section
-- module Solutions.OAIQ050_Laughlin.Laughlin_FourBody_Symmetry
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
-- module Solutions.OAIQ050_Laughlin.Laughlin_FiniteFlux_Gram08
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace Laughlin.Certificate
open scoped Matrix
theorem gram_8_s50_oai : gramRational 8 =
  !![0, 0, 0, 0;
    0, 720, -720, 1260;
    0, -720, 720, -1260;
    0, 1260, -1260, 2205] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact gram_8_1_1
  · exact gram_8_1_3
  · exact gram_8_1_5
  · exact gram_8_1_7
  · exact (Z_symm 8 3 1).trans gram_8_1_3
  · exact gram_8_3_3
  · exact gram_8_3_5
  · exact gram_8_3_7
  · exact (Z_symm 8 5 1).trans gram_8_1_5
  · exact (Z_symm 8 5 3).trans gram_8_3_5
  · exact gram_8_5_5
  · exact gram_8_5_7
  · exact (Z_symm 8 7 1).trans gram_8_1_7
  · exact (Z_symm 8 7 3).trans gram_8_3_7
  · exact (Z_symm 8 7 5).trans gram_8_5_7
  · exact gram_8_7_7

end Laughlin.Certificate

end OAI
end

theorem solution : type_of% @OAI.Laughlin.Certificate.gram_8_s50_oai := @OAI.Laughlin.Certificate.gram_8_s50_oai
