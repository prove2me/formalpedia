-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow4_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:38.820963+00:00
-- url     : https://prove2.me/submissions/70baab4a-e6cd-454d-9524-0a208d3a71ec

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_4_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow4_e_oai : ∀ j : Fin 27, Z 4 j =
    ∑ k, lowerUnit entries k 4 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_4_0_e
  · exact entry_4_1_e
  · exact entry_4_2_e
  · exact entry_4_3_e
  · exact entry_4_4_e
  · exact entry_4_5_e
  · exact entry_4_6_e
  · exact entry_4_7_e
  · exact entry_4_8_e
  · exact entry_4_9_e
  · exact entry_4_10_e
  · exact entry_4_11_e
  · exact entry_4_12_e
  · exact entry_4_13_e
  · exact entry_4_14_e
  · exact entry_4_15_e
  · exact entry_4_16_e
  · exact entry_4_17_e
  · exact entry_4_18_e
  · exact entry_4_19_e
  · exact entry_4_20_e
  · exact entry_4_21_e
  · exact entry_4_22_e
  · exact entry_4_23_e
  · exact entry_4_24_e
  · exact entry_4_25_e
  · exact entry_4_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow4_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow4_e_oai
