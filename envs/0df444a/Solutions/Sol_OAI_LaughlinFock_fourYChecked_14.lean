-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_14
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:28:51.515989+00:00
-- url     : https://prove2.me/submissions/ebb2108c-622c-41b5-802f-2fc9895cc5cf

import Mathlib
import Definitions.Def_OAIQ084L034
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_11_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_11_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_13_13
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_13_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_13_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_5_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_14_7_7
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_parts

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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1401
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1401. -/
namespace LaughlinFock

theorem collectedFourChecked_14_0 : collectNumericRowParts 14 0 = collectedFourData_14_0 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1403
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1403. -/
namespace LaughlinFock

theorem collectedFourChecked_14_1 : collectNumericRowParts 14 1 = collectedFourData_14_1 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1404
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1404. -/
namespace LaughlinFock

theorem collectedFourChecked_14_2 : collectNumericRowParts 14 2 = collectedFourData_14_2 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1406
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1406. -/
namespace LaughlinFock

theorem collectedFourChecked_14_3 : collectNumericRowParts 14 3 = collectedFourData_14_3 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1408
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1408. -/
namespace LaughlinFock

theorem collectedFourChecked_14_4 : collectNumericRowParts 14 4 = collectedFourData_14_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1410
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1410. -/
namespace LaughlinFock

theorem collectedFourChecked_14_5 : collectNumericRowParts 14 5 = collectedFourData_14_5 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1412
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1412. -/
namespace LaughlinFock

theorem collectedFourChecked_14_6 : collectNumericRowParts 14 6 = collectedFourData_14_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1413
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1413. -/
namespace LaughlinFock

theorem collectedFourChecked_14_7 : collectNumericRowParts 14 7 = collectedFourData_14_7 := by
  decide +kernel

theorem collectedFourChecked_14 (t : Fin 8) :
    collectNumericRowParts 14 t = collectedFourData_14 t := by
  fin_cases t
  · exact collectedFourChecked_14_0
  · exact collectedFourChecked_14_1
  · exact collectedFourChecked_14_2
  · exact collectedFourChecked_14_3
  · exact collectedFourChecked_14_4
  · exact collectedFourChecked_14_5
  · exact collectedFourChecked_14_6
  · exact collectedFourChecked_14_7

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_14_3_3 :
    (collectedFourPartsTrace 14 3 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (13386782195228438740574170659/67108864000000000000000) := by
  decide +kernel

theorem fourYNumber_14_5_3 :
    (collectedFourPartsTrace 14 5 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (-2673895873363342088813998569/104857600000000000000000) := by
  decide +kernel

theorem fourYNumber_14_7_3 :
    (collectedFourPartsTrace 14 7 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (80258770793485913472210966291/13421772800000000000000000) := by
  decide +kernel

theorem fourYNumber_14_7_5 :
    (collectedFourPartsTrace 14 7 5 collectedFourData_14 : ℚ) / fourCommonDenominator = (51791883792723030621502729521/13421772800000000000000000) := by
  decide +kernel

theorem fourYNumber_14_9_1 :
    (collectedFourPartsTrace 14 9 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (-65792859630351313043704679559/838860800000000000000000) := by
  decide +kernel

theorem fourYNumber_14_9_3 :
    (collectedFourPartsTrace 14 9 3 collectedFourData_14 : ℚ) / fourCommonDenominator = (11396787485992128812442905901/3355443200000000000000000) := by
  decide +kernel

theorem fourYNumber_14_9_5 :
    (collectedFourPartsTrace 14 9 5 collectedFourData_14 : ℚ) / fourCommonDenominator = (447947864118505342038286071/1677721600000000000000000) := by
  decide +kernel

theorem fourYNumber_14_9_7 :
    (collectedFourPartsTrace 14 9 7 collectedFourData_14 : ℚ) / fourCommonDenominator = (11786587097020001481424088313/13421772800000000000000000) := by
  decide +kernel

theorem fourYNumber_14_9_9 :
    (collectedFourPartsTrace 14 9 9 collectedFourData_14 : ℚ) / fourCommonDenominator = (-2511231860904985581654902337/3355443200000000000000000) := by
  decide +kernel

theorem fourYNumber_14_11_1 :
    (collectedFourPartsTrace 14 11 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (137254565014346724354426453723/671088640000000000000000) := by
  decide +kernel

theorem fourYNumber_14_11_5 :
    (collectedFourPartsTrace 14 11 5 collectedFourData_14 : ℚ) / fourCommonDenominator = (-199373232582573167162137599/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_14_11_7 :
    (collectedFourPartsTrace 14 11 7 collectedFourData_14 : ℚ) / fourCommonDenominator = (1148019225793308762774727077/26843545600000000000000000) := by
  decide +kernel

theorem fourYNumber_14_11_9 :
    (collectedFourPartsTrace 14 11 9 collectedFourData_14 : ℚ) / fourCommonDenominator = (-245216406486237366219564393/268435456000000000000000) := by
  decide +kernel

theorem fourYNumber_14_13_1 :
    (collectedFourPartsTrace 14 13 1 collectedFourData_14 : ℚ) / fourCommonDenominator = (-72085225343410427749643785743/104857600000000000000000) := by
  decide +kernel

theorem fourYNumber_14_13_7 :
    (collectedFourPartsTrace 14 13 7 collectedFourData_14 : ℚ) / fourCommonDenominator = (-472886193342561862517016363/671088640000000000000000) := by
  decide +kernel

theorem fourYNumber_14_13_9 :
    (collectedFourPartsTrace 14 13 9 collectedFourData_14 : ℚ) / fourCommonDenominator = (18739058037442034351954893713/3355443200000000000000000) := by
  decide +kernel

theorem fourYNumber_14_13_11 :
    (collectedFourPartsTrace 14 13 11 collectedFourData_14 : ℚ) / fourCommonDenominator = (-96382029030050639819612097/26843545600000000000000) := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate14
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate14. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_14 (r s : CopyLabel 14) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 14 r s = fourYData_14 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_14 collectedFourChecked_14]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_14_1_1
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
  · exact fourYNumber_14_3_1
  · exact fourYNumber_14_3_3
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
  · exact fourYNumber_14_5_1
  · exact fourYNumber_14_5_3
  · exact fourYNumber_14_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · have h : (13:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_14_7_1
  · exact fourYNumber_14_7_3
  · exact fourYNumber_14_7_5
  · exact fourYNumber_14_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_14_9_1
  · exact fourYNumber_14_9_3
  · exact fourYNumber_14_9_5
  · exact fourYNumber_14_9_7
  · exact fourYNumber_14_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_14_11_1
  · exact fourYNumber_14_11_3
  · exact fourYNumber_14_11_5
  · exact fourYNumber_14_11_7
  · exact fourYNumber_14_11_9
  · exact fourYNumber_14_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_14_13_1
  · exact fourYNumber_14_13_3
  · exact fourYNumber_14_13_5
  · exact fourYNumber_14_13_7
  · exact fourYNumber_14_13_9
  · exact fourYNumber_14_13_11
  · exact fourYNumber_14_13_13

theorem fourYChecked_14_oai (r s : CopyLabel 14) :
    integerRowsFourTrace 14 r s = fourYData_14 r s := by
  have hh : ∀ r s : CopyLabel 14, fourYData_14 r s = fourYData_14 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_14 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_14 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_14_oai := @OAI.LaughlinFock.fourYChecked_14_oai
