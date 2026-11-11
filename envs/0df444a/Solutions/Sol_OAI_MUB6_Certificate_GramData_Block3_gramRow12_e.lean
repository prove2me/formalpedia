-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow12_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:42.821605+00:00
-- url     : https://prove2.me/submissions/8a5633b7-2cc4-4467-93a9-4a73724f85b5

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_12_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow12_e_oai : ∀ j : Fin 27, Z 12 j =
    ∑ k, lowerUnit entries k 12 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_12_0_e
  · exact entry_12_1_e
  · exact entry_12_2_e
  · exact entry_12_3_e
  · exact entry_12_4_e
  · exact entry_12_5_e
  · exact entry_12_6_e
  · exact entry_12_7_e
  · exact entry_12_8_e
  · exact entry_12_9_e
  · exact entry_12_10_e
  · exact entry_12_11_e
  · exact entry_12_12_e
  · exact entry_12_13_e
  · exact entry_12_14_e
  · exact entry_12_15_e
  · exact entry_12_16_e
  · exact entry_12_17_e
  · exact entry_12_18_e
  · exact entry_12_19_e
  · exact entry_12_20_e
  · exact entry_12_21_e
  · exact entry_12_22_e
  · exact entry_12_23_e
  · exact entry_12_24_e
  · exact entry_12_25_e
  · exact entry_12_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow12_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow12_e_oai
