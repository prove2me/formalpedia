-- Prove2me | solution 1 for OAI.LaughlinFock.fourYChecked_8
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:49:51.855026+00:00
-- url     : https://prove2.me/submissions/7741fefb-ad6f-4f1d-bb79-83d273e5086c

import Mathlib
import Definitions.Def_OAIQ084L038
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_8_7_7
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0803
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0803. -/
namespace LaughlinFock

theorem collectedFourChecked_8_0 : collectNumericRowParts 8 0 = collectedFourData_8_0 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0807
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0807. -/
namespace LaughlinFock

theorem collectedFourChecked_8_1 : collectNumericRowParts 8 1 = collectedFourData_8_1 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0811
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0811. -/
namespace LaughlinFock

theorem collectedFourChecked_8_2 : collectNumericRowParts 8 2 = collectedFourData_8_2 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0816
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0816. -/
namespace LaughlinFock

theorem collectedFourChecked_8_3 : collectNumericRowParts 8 3 = collectedFourData_8_3 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0821
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0821. -/
namespace LaughlinFock

theorem collectedFourChecked_8_4 : collectNumericRowParts 8 4 = collectedFourData_8_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0826
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0826. -/
namespace LaughlinFock

theorem collectedFourChecked_8_5 : collectNumericRowParts 8 5 = collectedFourData_8_5 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0830
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0830. -/
namespace LaughlinFock

theorem collectedFourChecked_8_6 : collectNumericRowParts 8 6 = collectedFourData_8_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0833
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0833. -/
namespace LaughlinFock

theorem collectedFourChecked_8_7 : collectNumericRowParts 8 7 = collectedFourData_8_7 := by
  decide +kernel

theorem collectedFourChecked_8 (t : Fin 8) :
    collectNumericRowParts 8 t = collectedFourData_8 t := by
  fin_cases t
  · exact collectedFourChecked_8_0
  · exact collectedFourChecked_8_1
  · exact collectedFourChecked_8_2
  · exact collectedFourChecked_8_3
  · exact collectedFourChecked_8_4
  · exact collectedFourChecked_8_5
  · exact collectedFourChecked_8_6
  · exact collectedFourChecked_8_7

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_8_3_1 :
    (collectedFourPartsTrace 8 3 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (-1915756407095537127488603541/268435456000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_5_1 :
    (collectedFourPartsTrace 8 5 1 collectedFourData_8 : ℚ) / fourCommonDenominator = (5848046872621070751629176509/536870912000000000000000000) := by
  decide +kernel

theorem fourYNumber_8_7_5 :
    (collectedFourPartsTrace 8 7 5 collectedFourData_8 : ℚ) / fourCommonDenominator = (1770955193734196297743289949/536870912000000000000000000) := by
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
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate08
attribute [-instance] _root_.OAI.LaughlinFock.instDecidableEqFockRotationSpace _root_.OAI.LaughlinFock.instFintypeFockRotationSpace
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate08. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_8 (r s : CopyLabel 8) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 8 r s = fourYData_8 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_8 collectedFourChecked_8]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_8_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_8_3_1
  · exact fourYNumber_8_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_8_5_1
  · exact fourYNumber_8_5_3
  · exact fourYNumber_8_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_8_7_1
  · exact fourYNumber_8_7_3
  · exact fourYNumber_8_7_5
  · exact fourYNumber_8_7_7

theorem fourYChecked_8_oai (r s : CopyLabel 8) :
    integerRowsFourTrace 8 r s = fourYData_8 r s := by
  have hh : ∀ r s : CopyLabel 8, fourYData_8 r s = fourYData_8 s r := by
    apply @of_decide_eq_true _ (matrixEntriesDecidable _ _)
    decide +kernel
  by_cases h : s.val.val ≤ r.val.val
  · exact fourYLower_8 r s h
  · rw [integerRowsFourTrace_symm, fourYLower_8 s r (by omega), hh]

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYChecked_8_oai := @OAI.LaughlinFock.fourYChecked_8_oai
