-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_11
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:20:55.818766+00:00
-- url     : https://prove2.me/submissions/0fd6eba1-9993-4476-b80a-adbf03442ce4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_OAIQ084L031
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_11_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_7_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_9_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_9_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_11_9_9
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1102
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1102. -/
namespace LaughlinFock

theorem collectedFourChecked_11_0 : collectNumericRowParts 11 0 = collectedFourData_11_0 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1105
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1105. -/
namespace LaughlinFock

theorem collectedFourChecked_11_1 : collectNumericRowParts 11 1 = collectedFourData_11_1 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1108
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1108. -/
namespace LaughlinFock

theorem collectedFourChecked_11_2 : collectNumericRowParts 11 2 = collectedFourData_11_2 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1111
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1111. -/
namespace LaughlinFock

theorem collectedFourChecked_11_3 : collectNumericRowParts 11 3 = collectedFourData_11_3 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1115
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1115. -/
namespace LaughlinFock

theorem collectedFourChecked_11_4 : collectNumericRowParts 11 4 = collectedFourData_11_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1118
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1118. -/
namespace LaughlinFock

theorem collectedFourChecked_11_5 : collectNumericRowParts 11 5 = collectedFourData_11_5 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1122
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1122. -/
namespace LaughlinFock

theorem collectedFourChecked_11_6 : collectNumericRowParts 11 6 = collectedFourData_11_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse1124
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse1124. -/
namespace LaughlinFock

theorem collectedFourChecked_11_7 : collectNumericRowParts 11 7 = collectedFourData_11_7 := by
  decide +kernel

theorem collectedFourChecked_11 (t : Fin 8) :
    collectNumericRowParts 11 t = collectedFourData_11 t := by
  fin_cases t
  · exact collectedFourChecked_11_0
  · exact collectedFourChecked_11_1
  · exact collectedFourChecked_11_2
  · exact collectedFourChecked_11_3
  · exact collectedFourChecked_11_4
  · exact collectedFourChecked_11_5
  · exact collectedFourChecked_11_6
  · exact collectedFourChecked_11_7

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_11_1_1 :
    (collectedFourPartsTrace 11 1 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (355506999534679510671910366977/2684354560000000000000000) := by
  decide +kernel

theorem fourYNumber_11_5_1 :
    (collectedFourPartsTrace 11 5 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (4138293745048202697976148691/2684354560000000000000000) := by
  decide +kernel

theorem fourYNumber_11_7_1 :
    (collectedFourPartsTrace 11 7 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (-462687962608795946399629749/107374182400000000000000000) := by
  decide +kernel

theorem fourYNumber_11_7_5 :
    (collectedFourPartsTrace 11 7 5 collectedFourData_11 : ℚ) / fourCommonDenominator = (6557195925083744855698330017/214748364800000000000000000) := by
  decide +kernel

theorem fourYNumber_11_9_1 :
    (collectedFourPartsTrace 11 9 1 collectedFourData_11 : ℚ) / fourCommonDenominator = (11348337457149032083099347/8589934592000000000000) := by
  decide +kernel

theorem fourYNumber_11_9_5 :
    (collectedFourPartsTrace 11 9 5 collectedFourData_11 : ℚ) / fourCommonDenominator = (-54074165446495408903733637/1342177280000000000000000) := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate11
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate11. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_11 (r s : CopyLabel 11) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 11 r s = fourYData_11 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_11 collectedFourChecked_11]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_11_1_1
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
  · exact fourYNumber_11_3_1
  · exact fourYNumber_11_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · have h : (11:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_11_5_1
  · exact fourYNumber_11_5_3
  · exact fourYNumber_11_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · have h : (11:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_11_7_1
  · exact fourYNumber_11_7_3
  · exact fourYNumber_11_7_5
  · exact fourYNumber_11_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_11_9_1
  · exact fourYNumber_11_9_3
  · exact fourYNumber_11_9_5
  · exact fourYNumber_11_9_7
  · exact fourYNumber_11_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_11_11_1
  · exact fourYNumber_11_11_3
  · exact fourYNumber_11_11_5
  · exact fourYNumber_11_11_7
  · exact fourYNumber_11_11_9
  · exact fourYNumber_11_11_11

theorem fourYChecked_11_oai (r s : CopyLabel 11) :
    integerRowsFourTrace 11 r s = fourYData_11 r s := by
  have hh : ∀ r s : CopyLabel 11, fourYData_11 r s = fourYData_11 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_11 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_11 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_11_oai := @OAI.LaughlinFock.fourYChecked_11_oai
