-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow0_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:10.916426+00:00
-- url     : https://prove2.me/submissions/e862db88-c538-4e91-8e7a-058fbecacca5

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_0_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow0_e_oai : ∀ j : Fin 27, Z 0 j =
    ∑ k, lowerUnit entries k 0 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_0_0_e
  · exact entry_0_1_e
  · exact entry_0_2_e
  · exact entry_0_3_e
  · exact entry_0_4_e
  · exact entry_0_5_e
  · exact entry_0_6_e
  · exact entry_0_7_e
  · exact entry_0_8_e
  · exact entry_0_9_e
  · exact entry_0_10_e
  · exact entry_0_11_e
  · exact entry_0_12_e
  · exact entry_0_13_e
  · exact entry_0_14_e
  · exact entry_0_15_e
  · exact entry_0_16_e
  · exact entry_0_17_e
  · exact entry_0_18_e
  · exact entry_0_19_e
  · exact entry_0_20_e
  · exact entry_0_21_e
  · exact entry_0_22_e
  · exact entry_0_23_e
  · exact entry_0_24_e
  · exact entry_0_25_e
  · exact entry_0_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow0_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow0_e_oai
