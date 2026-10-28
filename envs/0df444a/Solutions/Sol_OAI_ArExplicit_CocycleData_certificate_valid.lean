-- Prove2me | solution 1 for OAI.ArExplicit.CocycleData.certificate_valid
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-27T13:43:16.141064+00:00
-- url     : https://prove2.me/submissions/1df1e7e5-003b-47db-adbd-1e9bafbebead

import Mathlib
import Definitions.Def_OAIQ031A000
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_e
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_f
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_j
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_n
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_t
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_u
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_v
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_x
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_y
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_false_z
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_e
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_f
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_j
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_n
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_t
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_u
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_v
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_x
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_y
import Theorems.Thm_OAI_ArExplicit_CocycleData_valid_true_z

section
-- module Solutions.OAIQ031_AR.AuslanderReiten_Cocycles_CocycleCertificate
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace ArExplicit.CocycleData

theorem certificate_valid_oai (a : TIndex) : certificate a = true := by
  obtain ⟨b, i⟩ := a
  cases b <;> cases i
  · exact valid_false_e
  · exact valid_false_x
  · exact valid_false_y
  · exact valid_false_z
  · exact valid_false_u
  · exact valid_false_v
  · exact valid_false_t
  · exact valid_false_j
  · exact valid_false_f
  · exact valid_false_n
  · exact valid_true_e
  · exact valid_true_x
  · exact valid_true_y
  · exact valid_true_z
  · exact valid_true_u
  · exact valid_true_v
  · exact valid_true_t
  · exact valid_true_j
  · exact valid_true_f
  · exact valid_true_n

end ArExplicit.CocycleData

end OAI
end

theorem solution : type_of% @OAI.ArExplicit.CocycleData.certificate_valid_oai := @OAI.ArExplicit.CocycleData.certificate_valid_oai
