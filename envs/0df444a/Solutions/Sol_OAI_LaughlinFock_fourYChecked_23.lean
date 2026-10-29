-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_23
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:45:51.52+00:00
-- url     : https://prove2.me/submissions/9af535c4-f933-4f50-8266-b37e962fb8b2

import Mathlib
import Definitions.Def_OAIQ084L027
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_collected

section
-- module Solutions.OAIQ084_LF.LaughlinFock_RowTraces
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Row Traces. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexConjugate ComplexOrder
open Filter Topology



theorem rowFourLevel_symm {t : ℕ} (b c : RowEntry t) :
    rowFourLevel b c = rowFourLevel c b := by
  have hb := (rowEntry_bounds b).2.2.2
  have hc := (rowEntry_bounds c).2.2.2
  dsimp [rowFourLevel]
  omega

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse23
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse23. -/
namespace LaughlinFock

theorem collectedFourChecked_23 : collectedFourTerms 23 = collectedFourData_23 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_23_1_1 :
    (collectedFourTrace 23 1 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_3_1 :
    (collectedFourTrace 23 3 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_3_3 :
    (collectedFourTrace 23 3 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_1 :
    (collectedFourTrace 23 5 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_3 :
    (collectedFourTrace 23 5 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_5_5 :
    (collectedFourTrace 23 5 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_1 :
    (collectedFourTrace 23 7 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_3 :
    (collectedFourTrace 23 7 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_5 :
    (collectedFourTrace 23 7 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_7_7 :
    (collectedFourTrace 23 7 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_1 :
    (collectedFourTrace 23 9 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_3 :
    (collectedFourTrace 23 9 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_5 :
    (collectedFourTrace 23 9 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_7 :
    (collectedFourTrace 23 9 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_9_9 :
    (collectedFourTrace 23 9 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_1 :
    (collectedFourTrace 23 11 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_3 :
    (collectedFourTrace 23 11 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_5 :
    (collectedFourTrace 23 11 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_7 :
    (collectedFourTrace 23 11 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_9 :
    (collectedFourTrace 23 11 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_11_11 :
    (collectedFourTrace 23 11 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_1 :
    (collectedFourTrace 23 13 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_3 :
    (collectedFourTrace 23 13 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_5 :
    (collectedFourTrace 23 13 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_7 :
    (collectedFourTrace 23 13 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_9 :
    (collectedFourTrace 23 13 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_11 :
    (collectedFourTrace 23 13 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_13_13 :
    (collectedFourTrace 23 13 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_1 :
    (collectedFourTrace 23 15 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_3 :
    (collectedFourTrace 23 15 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_5 :
    (collectedFourTrace 23 15 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_7 :
    (collectedFourTrace 23 15 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_9 :
    (collectedFourTrace 23 15 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_11 :
    (collectedFourTrace 23 15 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_13 :
    (collectedFourTrace 23 15 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_15_15 :
    (collectedFourTrace 23 15 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_1 :
    (collectedFourTrace 23 17 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_3 :
    (collectedFourTrace 23 17 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_5 :
    (collectedFourTrace 23 17 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_7 :
    (collectedFourTrace 23 17 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_9 :
    (collectedFourTrace 23 17 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_11 :
    (collectedFourTrace 23 17 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_13 :
    (collectedFourTrace 23 17 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_15 :
    (collectedFourTrace 23 17 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_17_17 :
    (collectedFourTrace 23 17 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_1 :
    (collectedFourTrace 23 19 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_3 :
    (collectedFourTrace 23 19 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_5 :
    (collectedFourTrace 23 19 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_7 :
    (collectedFourTrace 23 19 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_9 :
    (collectedFourTrace 23 19 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_11 :
    (collectedFourTrace 23 19 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_13 :
    (collectedFourTrace 23 19 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_15 :
    (collectedFourTrace 23 19 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_17 :
    (collectedFourTrace 23 19 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_19_19 :
    (collectedFourTrace 23 19 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_1 :
    (collectedFourTrace 23 21 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_3 :
    (collectedFourTrace 23 21 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_5 :
    (collectedFourTrace 23 21 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_7 :
    (collectedFourTrace 23 21 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_9 :
    (collectedFourTrace 23 21 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_11 :
    (collectedFourTrace 23 21 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_13 :
    (collectedFourTrace 23 21 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_15 :
    (collectedFourTrace 23 21 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_17 :
    (collectedFourTrace 23 21 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_19 :
    (collectedFourTrace 23 21 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_21_21 :
    (collectedFourTrace 23 21 21 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_1 :
    (collectedFourTrace 23 23 1 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_3 :
    (collectedFourTrace 23 23 3 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_5 :
    (collectedFourTrace 23 23 5 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_7 :
    (collectedFourTrace 23 23 7 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_9 :
    (collectedFourTrace 23 23 9 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_11 :
    (collectedFourTrace 23 23 11 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_13 :
    (collectedFourTrace 23 23 13 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_15 :
    (collectedFourTrace 23 23 15 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_17 :
    (collectedFourTrace 23 23 17 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_19 :
    (collectedFourTrace 23 23 19 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_21 :
    (collectedFourTrace 23 23 21 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

theorem fourYNumber_23_23_23 :
    (collectedFourTrace 23 23 23 collectedFourData_23 : ℚ) / fourCommonDenominator = 0 := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_TraceSymmetry
attribute [-instance] _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Trace Symmetry. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem rationalFourFactor_symm {t : ℕ} (D : ℕ) (b c : RowEntry t) :
    rationalFourFactor D b c = rationalFourFactor D c b := by
  unfold rationalFourFactor
  rw [rowFourLevel_symm b c]
  ring

theorem integerFourTrace_symm (D t : ℕ) (a : RowEntry t → ℚ) (r s : CopyLabel D) :
    integerFourTrace D t a r s = integerFourTrace D t a s r := by
  unfold integerFourTrace
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  rw [rowFourLevel_symm c b, rationalFourFactor_symm D c b]
  split_ifs <;> ring

theorem integerRowsFourTrace_symm (D : ℕ) (r s : CopyLabel D) :
    integerRowsFourTrace D r s = integerRowsFourTrace D s r := by
  unfold integerRowsFourTrace
  simp only [Matrix.sum_apply]
  exact Finset.sum_congr rfl (fun t _ => integerFourTrace_symm D t.val (certificateAlpha t) r s)

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate23
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate23. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_23 (r s : CopyLabel 23) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 23 r s = fourYData_23 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_23 collectedFourChecked_23]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_23_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · have h : (11:ℕ) ≤ 1 := hrs
    omega
  · have h : (13:ℕ) ≤ 1 := hrs
    omega
  · have h : (15:ℕ) ≤ 1 := hrs
    omega
  · have h : (17:ℕ) ≤ 1 := hrs
    omega
  · have h : (19:ℕ) ≤ 1 := hrs
    omega
  · have h : (21:ℕ) ≤ 1 := hrs
    omega
  · have h : (23:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_23_3_1
  · exact fourYNumber_23_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · have h : (13:ℕ) ≤ 3 := hrs
    omega
  · have h : (15:ℕ) ≤ 3 := hrs
    omega
  · have h : (17:ℕ) ≤ 3 := hrs
    omega
  · have h : (19:ℕ) ≤ 3 := hrs
    omega
  · have h : (21:ℕ) ≤ 3 := hrs
    omega
  · have h : (23:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_23_5_1
  · exact fourYNumber_23_5_3
  · exact fourYNumber_23_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · have h : (15:ℕ) ≤ 5 := hrs
    omega
  · have h : (17:ℕ) ≤ 5 := hrs
    omega
  · have h : (19:ℕ) ≤ 5 := hrs
    omega
  · have h : (21:ℕ) ≤ 5 := hrs
    omega
  · have h : (23:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_23_7_1
  · exact fourYNumber_23_7_3
  · exact fourYNumber_23_7_5
  · exact fourYNumber_23_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · have h : (17:ℕ) ≤ 7 := hrs
    omega
  · have h : (19:ℕ) ≤ 7 := hrs
    omega
  · have h : (21:ℕ) ≤ 7 := hrs
    omega
  · have h : (23:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_23_9_1
  · exact fourYNumber_23_9_3
  · exact fourYNumber_23_9_5
  · exact fourYNumber_23_9_7
  · exact fourYNumber_23_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · have h : (17:ℕ) ≤ 9 := hrs
    omega
  · have h : (19:ℕ) ≤ 9 := hrs
    omega
  · have h : (21:ℕ) ≤ 9 := hrs
    omega
  · have h : (23:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_23_11_1
  · exact fourYNumber_23_11_3
  · exact fourYNumber_23_11_5
  · exact fourYNumber_23_11_7
  · exact fourYNumber_23_11_9
  · exact fourYNumber_23_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · have h : (17:ℕ) ≤ 11 := hrs
    omega
  · have h : (19:ℕ) ≤ 11 := hrs
    omega
  · have h : (21:ℕ) ≤ 11 := hrs
    omega
  · have h : (23:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_23_13_1
  · exact fourYNumber_23_13_3
  · exact fourYNumber_23_13_5
  · exact fourYNumber_23_13_7
  · exact fourYNumber_23_13_9
  · exact fourYNumber_23_13_11
  · exact fourYNumber_23_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · have h : (17:ℕ) ≤ 13 := hrs
    omega
  · have h : (19:ℕ) ≤ 13 := hrs
    omega
  · have h : (21:ℕ) ≤ 13 := hrs
    omega
  · have h : (23:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_23_15_1
  · exact fourYNumber_23_15_3
  · exact fourYNumber_23_15_5
  · exact fourYNumber_23_15_7
  · exact fourYNumber_23_15_9
  · exact fourYNumber_23_15_11
  · exact fourYNumber_23_15_13
  · exact fourYNumber_23_15_15
  · have h : (17:ℕ) ≤ 15 := hrs
    omega
  · have h : (19:ℕ) ≤ 15 := hrs
    omega
  · have h : (21:ℕ) ≤ 15 := hrs
    omega
  · have h : (23:ℕ) ≤ 15 := hrs
    omega
  · exact fourYNumber_23_17_1
  · exact fourYNumber_23_17_3
  · exact fourYNumber_23_17_5
  · exact fourYNumber_23_17_7
  · exact fourYNumber_23_17_9
  · exact fourYNumber_23_17_11
  · exact fourYNumber_23_17_13
  · exact fourYNumber_23_17_15
  · exact fourYNumber_23_17_17
  · have h : (19:ℕ) ≤ 17 := hrs
    omega
  · have h : (21:ℕ) ≤ 17 := hrs
    omega
  · have h : (23:ℕ) ≤ 17 := hrs
    omega
  · exact fourYNumber_23_19_1
  · exact fourYNumber_23_19_3
  · exact fourYNumber_23_19_5
  · exact fourYNumber_23_19_7
  · exact fourYNumber_23_19_9
  · exact fourYNumber_23_19_11
  · exact fourYNumber_23_19_13
  · exact fourYNumber_23_19_15
  · exact fourYNumber_23_19_17
  · exact fourYNumber_23_19_19
  · have h : (21:ℕ) ≤ 19 := hrs
    omega
  · have h : (23:ℕ) ≤ 19 := hrs
    omega
  · exact fourYNumber_23_21_1
  · exact fourYNumber_23_21_3
  · exact fourYNumber_23_21_5
  · exact fourYNumber_23_21_7
  · exact fourYNumber_23_21_9
  · exact fourYNumber_23_21_11
  · exact fourYNumber_23_21_13
  · exact fourYNumber_23_21_15
  · exact fourYNumber_23_21_17
  · exact fourYNumber_23_21_19
  · exact fourYNumber_23_21_21
  · have h : (23:ℕ) ≤ 21 := hrs
    omega
  · exact fourYNumber_23_23_1
  · exact fourYNumber_23_23_3
  · exact fourYNumber_23_23_5
  · exact fourYNumber_23_23_7
  · exact fourYNumber_23_23_9
  · exact fourYNumber_23_23_11
  · exact fourYNumber_23_23_13
  · exact fourYNumber_23_23_15
  · exact fourYNumber_23_23_17
  · exact fourYNumber_23_23_19
  · exact fourYNumber_23_23_21
  · exact fourYNumber_23_23_23

theorem fourYChecked_23_oai (r s : CopyLabel 23) :
    integerRowsFourTrace 23 r s = fourYData_23 r s := by
  have hh : ∀ r s : CopyLabel 23, fourYData_23 r s = fourYData_23 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_23 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_23 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_23_oai := @OAI.LaughlinFock.fourYChecked_23_oai
