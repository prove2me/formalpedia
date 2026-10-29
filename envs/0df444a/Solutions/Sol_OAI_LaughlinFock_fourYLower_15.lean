-- Prove2me | solution 1 for OAI.LaughlinFock.fourYLower_15
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T23:01:02.473053+00:00
-- url     : https://prove2.me/submissions/df57820a-9ae0-4ae7-b331-05635ef8d9c0

import Mathlib
import Definitions.Def_OAIQ084L029
import Definitions.Def_OAIQ084L043
import Theorems.Thm_OAI_LaughlinFock_collectedFourChecked_15
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_11_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_13
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_13_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_11
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_13
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_15
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_15_9
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_1_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_3_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_3_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_5_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_5_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_5_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_7_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_7_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_7_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_7_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_9_1
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_9_3
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_9_5
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_9_7
import Theorems.Thm_OAI_LaughlinFock_fourYNumber_15_9_9
import Theorems.Thm_OAI_LaughlinFock_integerRowsFourTrace_collected

section
-- module Solutions.OAIQ084_LF.LaughlinFock_Certificate15
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Certificate15. -/
noncomputable section
namespace LaughlinFock
open scoped BigOperators Matrix ComplexOrder

theorem fourYLower_15_oai (r s : CopyLabel 15) (hrs : s.val.val ≤ r.val.val) :
    integerRowsFourTrace 15 r s = fourYData_15 r s := by
  rw [integerRowsFourTrace_collected (by decide) collectedFourData_15 collectedFourChecked_15]
  fin_cases r <;> fin_cases s
  · exact fourYNumber_15_1_1
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
  · exact fourYNumber_15_3_1
  · exact fourYNumber_15_3_3
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
  · exact fourYNumber_15_5_1
  · exact fourYNumber_15_5_3
  · exact fourYNumber_15_5_5
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
  · exact fourYNumber_15_7_1
  · exact fourYNumber_15_7_3
  · exact fourYNumber_15_7_5
  · exact fourYNumber_15_7_7
  · have h : (9:ℕ) ≤ 7 := hrs
    omega
  · have h : (11:ℕ) ≤ 7 := hrs
    omega
  · have h : (13:ℕ) ≤ 7 := hrs
    omega
  · have h : (15:ℕ) ≤ 7 := hrs
    omega
  · exact fourYNumber_15_9_1
  · exact fourYNumber_15_9_3
  · exact fourYNumber_15_9_5
  · exact fourYNumber_15_9_7
  · exact fourYNumber_15_9_9
  · have h : (11:ℕ) ≤ 9 := hrs
    omega
  · have h : (13:ℕ) ≤ 9 := hrs
    omega
  · have h : (15:ℕ) ≤ 9 := hrs
    omega
  · exact fourYNumber_15_11_1
  · exact fourYNumber_15_11_3
  · exact fourYNumber_15_11_5
  · exact fourYNumber_15_11_7
  · exact fourYNumber_15_11_9
  · exact fourYNumber_15_11_11
  · have h : (13:ℕ) ≤ 11 := hrs
    omega
  · have h : (15:ℕ) ≤ 11 := hrs
    omega
  · exact fourYNumber_15_13_1
  · exact fourYNumber_15_13_3
  · exact fourYNumber_15_13_5
  · exact fourYNumber_15_13_7
  · exact fourYNumber_15_13_9
  · exact fourYNumber_15_13_11
  · exact fourYNumber_15_13_13
  · have h : (15:ℕ) ≤ 13 := hrs
    omega
  · exact fourYNumber_15_15_1
  · exact fourYNumber_15_15_3
  · exact fourYNumber_15_15_5
  · exact fourYNumber_15_15_7
  · exact fourYNumber_15_15_9
  · exact fourYNumber_15_15_11
  · exact fourYNumber_15_15_13
  · exact fourYNumber_15_15_15

end LaughlinFock
end

end OAI
end

theorem solution : type_of% @OAI.LaughlinFock.fourYLower_15_oai := @OAI.LaughlinFock.fourYLower_15_oai
