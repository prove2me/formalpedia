-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:48.945165+00:00
-- url     : https://prove2.me/submissions/2450d4ea-64a7-425f-ac6f-4f46a5f6e067

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_16_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow16_e_oai : ∀ j : Fin 27, Z 16 j =
    ∑ k, lowerUnit entries k 16 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_16_0_e
  · exact entry_16_1_e
  · exact entry_16_2_e
  · exact entry_16_3_e
  · exact entry_16_4_e
  · exact entry_16_5_e
  · exact entry_16_6_e
  · exact entry_16_7_e
  · exact entry_16_8_e
  · exact entry_16_9_e
  · exact entry_16_10_e
  · exact entry_16_11_e
  · exact entry_16_12_e
  · exact entry_16_13_e
  · exact entry_16_14_e
  · exact entry_16_15_e
  · exact entry_16_16_e
  · exact entry_16_17_e
  · exact entry_16_18_e
  · exact entry_16_19_e
  · exact entry_16_20_e
  · exact entry_16_21_e
  · exact entry_16_22_e
  · exact entry_16_23_e
  · exact entry_16_24_e
  · exact entry_16_25_e
  · exact entry_16_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow16_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow16_e_oai
