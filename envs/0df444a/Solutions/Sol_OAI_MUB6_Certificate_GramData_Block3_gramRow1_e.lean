-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow1_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:46.639975+00:00
-- url     : https://prove2.me/submissions/2abe57a5-40d8-48a4-b652-2678f6521da8

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_1_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow1_e_oai : ∀ j : Fin 27, Z 1 j =
    ∑ k, lowerUnit entries k 1 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_1_0_e
  · exact entry_1_1_e
  · exact entry_1_2_e
  · exact entry_1_3_e
  · exact entry_1_4_e
  · exact entry_1_5_e
  · exact entry_1_6_e
  · exact entry_1_7_e
  · exact entry_1_8_e
  · exact entry_1_9_e
  · exact entry_1_10_e
  · exact entry_1_11_e
  · exact entry_1_12_e
  · exact entry_1_13_e
  · exact entry_1_14_e
  · exact entry_1_15_e
  · exact entry_1_16_e
  · exact entry_1_17_e
  · exact entry_1_18_e
  · exact entry_1_19_e
  · exact entry_1_20_e
  · exact entry_1_21_e
  · exact entry_1_22_e
  · exact entry_1_23_e
  · exact entry_1_24_e
  · exact entry_1_25_e
  · exact entry_1_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow1_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow1_e_oai
