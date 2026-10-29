-- Prove2me | solution 1 for OAI.LaughlinFock.fourYLower_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T20:59:57.300854+00:00
-- url     : https://prove2.me/submissions/4beadc00-bdea-4592-84dd-6056ddfa8f31

import Mathlib
import Definitions.Def_OAIQ084L039
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_7_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_9_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_9_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_9_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_9_9_9
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_parts

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0903
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0903. -/
namespace LaughlinFock

theorem collectedFourChecked_9_0 : collectNumericRowParts 9 0 = collectedFourData_9_0 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0906
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0906. -/
namespace LaughlinFock

theorem collectedFourChecked_9_1 : collectNumericRowParts 9 1 = collectedFourData_9_1 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0910
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0910. -/
namespace LaughlinFock

theorem collectedFourChecked_9_2 : collectNumericRowParts 9 2 = collectedFourData_9_2 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0915
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0915. -/
namespace LaughlinFock

theorem collectedFourChecked_9_3 : collectNumericRowParts 9 3 = collectedFourData_9_3 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0919
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0919. -/
namespace LaughlinFock

theorem collectedFourChecked_9_4 : collectNumericRowParts 9 4 = collectedFourData_9_4 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0923
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0923. -/
namespace LaughlinFock

theorem collectedFourChecked_9_5 : collectNumericRowParts 9 5 = collectedFourData_9_5 := by
  decide +kernel
end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0927
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0927. -/
namespace LaughlinFock

theorem collectedFourChecked_9_6 : collectNumericRowParts 9 6 = collectedFourData_9_6 := by
  decide +kernel

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Sparse0930
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Sparse0930. -/
namespace LaughlinFock

theorem collectedFourChecked_9_7 : collectNumericRowParts 9 7 = collectedFourData_9_7 := by
  decide +kernel

theorem collectedFourChecked_9 (t : Fin 8) :
    collectNumericRowParts 9 t = collectedFourData_9 t := by
  fin_cases t
  · exact collectedFourChecked_9_0
  · exact collectedFourChecked_9_1
  · exact collectedFourChecked_9_2
  · exact collectedFourChecked_9_3
  · exact collectedFourChecked_9_4
  · exact collectedFourChecked_9_5
  · exact collectedFourChecked_9_6
  · exact collectedFourChecked_9_7

end LaughlinFock

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09Data
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09 Data. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder



theorem fourYNumber_9_5_1 :
    (collectedFourPartsTrace 9 5 1 collectedFourData_9 : ℚ) / fourCommonDenominator = (260469020419292216479075761/53687091200000000000000000) := by
  decide +kernel

theorem fourYNumber_9_7_3 :
    (collectedFourPartsTrace 9 7 3 collectedFourData_9 : ℚ) / fourCommonDenominator = (-1837610439668880684708642399/171798691840000000000000000) := by
  decide +kernel

theorem fourYNumber_9_7_5 :
    (collectedFourPartsTrace 9 7 5 collectedFourData_9 : ℚ) / fourCommonDenominator = (1660933205203877918300823867/268435456000000000000000000) := by
  decide +kernel

theorem fourYNumber_9_9_5 :
    (collectedFourPartsTrace 9 9 5 collectedFourData_9 : ℚ) / fourCommonDenominator = (7156024769090901250266984873/536870912000000000000000000) := by
  decide +kernel

end LaughlinFock
end

end OAI
end

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate09
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate09. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_9_oai (r s : CopyLabel 9) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 9 r s = fourYData_9 r s := by
  rw [integerRowsFourTrace_parts (by decide) collectedFourData_9 collectedFourChecked_9]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_9_1_1
  · have h : (3:ℕ) ≤ 1 := hrs
    omega
  · have h : (5:ℕ) ≤ 1 := hrs
    omega
  · have h : (7:ℕ) ≤ 1 := hrs
    omega
  · have h : (9:ℕ) ≤ 1 := hrs
    omega
  · exact fourYNumber_9_3_1
  · exact fourYNumber_9_3_3
  · have h : (5:ℕ) ≤ 3 := hrs
    omega
  · have h : (7:ℕ) ≤ 3 := hrs
    omega
  · have h : (9:ℕ) ≤ 3 := hrs
    omega
  · exact fourYNumber_9_5_1
  · exact fourYNumber_9_5_3
  · exact fourYNumber_9_5_5
  · have h : (7:ℕ) ≤ 5 := hrs
    omega
  · have h : (9:ℕ) ≤ 5 := hrs
    omega
  · exact fourYNumber_9_7_1
  · exact fourYNumber_9_7_3
  · exact fourYNumber_9_7_5
  · exact fourYNumber_9_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_9_9_1
  · exact fourYNumber_9_9_3
  · exact fourYNumber_9_9_5
  · exact fourYNumber_9_9_7
  · exact fourYNumber_9_9_9

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYLower_9_oai := @OAI.LaughlinFock.fourYLower_9_oai
