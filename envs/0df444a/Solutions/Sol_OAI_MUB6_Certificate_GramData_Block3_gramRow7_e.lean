-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow7_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:21.037197+00:00
-- url     : https://prove2.me/submissions/22ad72db-a984-42b7-9800-971c8eb6091c

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_7_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow7_e_oai : ∀ j : Fin 27, Z 7 j =
    ∑ k, lowerUnit entries k 7 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_7_0_e
  · exact entry_7_1_e
  · exact entry_7_2_e
  · exact entry_7_3_e
  · exact entry_7_4_e
  · exact entry_7_5_e
  · exact entry_7_6_e
  · exact entry_7_7_e
  · exact entry_7_8_e
  · exact entry_7_9_e
  · exact entry_7_10_e
  · exact entry_7_11_e
  · exact entry_7_12_e
  · exact entry_7_13_e
  · exact entry_7_14_e
  · exact entry_7_15_e
  · exact entry_7_16_e
  · exact entry_7_17_e
  · exact entry_7_18_e
  · exact entry_7_19_e
  · exact entry_7_20_e
  · exact entry_7_21_e
  · exact entry_7_22_e
  · exact entry_7_23_e
  · exact entry_7_24_e
  · exact entry_7_25_e
  · exact entry_7_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow7_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow7_e_oai
