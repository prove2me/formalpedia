-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow22_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:43.373918+00:00
-- url     : https://prove2.me/submissions/6c7b3330-4e90-44f1-a8aa-eb28e4098001

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_22_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow22_e_oai : ∀ j : Fin 27, Z 22 j =
    ∑ k, lowerUnit entries k 22 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_22_0_e
  · exact entry_22_1_e
  · exact entry_22_2_e
  · exact entry_22_3_e
  · exact entry_22_4_e
  · exact entry_22_5_e
  · exact entry_22_6_e
  · exact entry_22_7_e
  · exact entry_22_8_e
  · exact entry_22_9_e
  · exact entry_22_10_e
  · exact entry_22_11_e
  · exact entry_22_12_e
  · exact entry_22_13_e
  · exact entry_22_14_e
  · exact entry_22_15_e
  · exact entry_22_16_e
  · exact entry_22_17_e
  · exact entry_22_18_e
  · exact entry_22_19_e
  · exact entry_22_20_e
  · exact entry_22_21_e
  · exact entry_22_22_e
  · exact entry_22_23_e
  · exact entry_22_24_e
  · exact entry_22_25_e
  · exact entry_22_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow22_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow22_e_oai
