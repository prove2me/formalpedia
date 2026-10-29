-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_10
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:19:47.843472+00:00
-- url     : https://prove2.me/submissions/5311c54c-c2fd-4b5f-a367-7b932f66a0d7

import Mathlib
import Definitions.Def_OAIQ084L030
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_7_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_7_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_9_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_9_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_9_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_10_9_9
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1003
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1003. -/
namespace LaughlinFock

theorem collectedFourChecked_10_0 : collectNumericRowParts 10 0 = collectedFourData_10_0 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1006
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1006. -/
namespace LaughlinFock

theorem collectedFourChecked_10_1 : collectNumericRowParts 10 1 = collectedFourData_10_1 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1009
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1009. -/
namespace LaughlinFock

theorem collectedFourChecked_10_2 : collectNumericRowParts 10 2 = collectedFourData_10_2 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1013
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1013. -/
namespace LaughlinFock

theorem collectedFourChecked_10_3 : collectNumericRowParts 10 3 = collectedFourData_10_3 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1017
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1017. -/
namespace LaughlinFock

theorem collectedFourChecked_10_4 : collectNumericRowParts 10 4 = collectedFourData_10_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1021
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1021. -/
namespace LaughlinFock

theorem collectedFourChecked_10_5 : collectNumericRowParts 10 5 = collectedFourData_10_5 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1024
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1024. -/
namespace LaughlinFock

theorem collectedFourChecked_10_6 : collectNumericRowParts 10 6 = collectedFourData_10_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1027
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1027. -/
namespace LaughlinFock

theorem collectedFourChecked_10_7 : collectNumericRowParts 10 7 = collectedFourData_10_7 := by
  decide +kernel

theorem collectedFourChecked_10 (t : Fin 8) :
    collectNumericRowParts 10 t = collectedFourData_10 t := by
  fin_cases t
  · exact collectedFourChecked_10_0
  · exact collectedFourChecked_10_1
  · exact collectedFourChecked_10_2
  · exact collectedFourChecked_10_3
  · exact collectedFourChecked_10_4
  · exact collectedFourChecked_10_5
  · exact collectedFourChecked_10_6
  · exact collectedFourChecked_10_7

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_10_3_3 :
    (collectedFourPartsTrace 10 3 3 collectedFourData_10 : ℚ) / fourCommonDenominator = (6753716923485661803328277187/67108864000000000000000000) := by
  decide +kernel

theorem fourYNumber_10_5_1 :
    (collectedFourPartsTrace 10 5 1 collectedFourData_10 : ℚ) / fourCommonDenominator = (148518328795926257133899451/134217728000000000000000) := by
  decide +kernel

theorem fourYNumber_10_5_3 :
    (collectedFourPartsTrace 10 5 3 collectedFourData_10 : ℚ) / fourCommonDenominator = (-133847515145750760226034487/1342177280000000000000000) := by
  decide +kernel

theorem fourYNumber_10_9_5 :
    (collectedFourPartsTrace 10 9 5 collectedFourData_10 : ℚ) / fourCommonDenominator = (79913088812449654011001179/1342177280000000000000000) := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate10
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate10. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_10 (r s : CopyLabel 10) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 10 r s = fourYData_10 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_10 collectedFourChecked_10]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_10_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_10_3_1
  · exact fourYNumber_10_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_10_5_1
  · exact fourYNumber_10_5_3
  · exact fourYNumber_10_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_10_7_1
  · exact fourYNumber_10_7_3
  · exact fourYNumber_10_7_5
  · exact fourYNumber_10_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_10_9_1
  · exact fourYNumber_10_9_3
  · exact fourYNumber_10_9_5
  · exact fourYNumber_10_9_7
  · exact fourYNumber_10_9_9

theorem fourYChecked_10_oai (r s : CopyLabel 10) :
    integerRowsFourTrace 10 r s = fourYData_10 r s := by
  have hh : ∀ r s : CopyLabel 10, fourYData_10 r s = fourYData_10 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_10 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_10 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_10_oai := @OAI.LaughlinFock.fourYChecked_10_oai
