-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow5_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:34.915794+00:00
-- url     : https://prove2.me/submissions/cdacdcea-d9ed-482d-b0fc-67ccaeb1913b

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_5_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow5_e_oai : ∀ j : Fin 27, Z 5 j =
    ∑ k, lowerUnit entries k 5 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_5_0_e
  · exact entry_5_1_e
  · exact entry_5_2_e
  · exact entry_5_3_e
  · exact entry_5_4_e
  · exact entry_5_5_e
  · exact entry_5_6_e
  · exact entry_5_7_e
  · exact entry_5_8_e
  · exact entry_5_9_e
  · exact entry_5_10_e
  · exact entry_5_11_e
  · exact entry_5_12_e
  · exact entry_5_13_e
  · exact entry_5_14_e
  · exact entry_5_15_e
  · exact entry_5_16_e
  · exact entry_5_17_e
  · exact entry_5_18_e
  · exact entry_5_19_e
  · exact entry_5_20_e
  · exact entry_5_21_e
  · exact entry_5_22_e
  · exact entry_5_23_e
  · exact entry_5_24_e
  · exact entry_5_25_e
  · exact entry_5_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow5_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow5_e_oai
