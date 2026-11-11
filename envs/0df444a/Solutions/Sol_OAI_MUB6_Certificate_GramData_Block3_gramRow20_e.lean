-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow20_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:45.758185+00:00
-- url     : https://prove2.me/submissions/bd8121c7-fa68-4c73-8e06-299a5d516d03

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_20_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow20_e_oai : ∀ j : Fin 27, Z 20 j =
    ∑ k, lowerUnit entries k 20 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_20_0_e
  · exact entry_20_1_e
  · exact entry_20_2_e
  · exact entry_20_3_e
  · exact entry_20_4_e
  · exact entry_20_5_e
  · exact entry_20_6_e
  · exact entry_20_7_e
  · exact entry_20_8_e
  · exact entry_20_9_e
  · exact entry_20_10_e
  · exact entry_20_11_e
  · exact entry_20_12_e
  · exact entry_20_13_e
  · exact entry_20_14_e
  · exact entry_20_15_e
  · exact entry_20_16_e
  · exact entry_20_17_e
  · exact entry_20_18_e
  · exact entry_20_19_e
  · exact entry_20_20_e
  · exact entry_20_21_e
  · exact entry_20_22_e
  · exact entry_20_23_e
  · exact entry_20_24_e
  · exact entry_20_25_e
  · exact entry_20_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow20_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow20_e_oai
