-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:48.548838+00:00
-- url     : https://prove2.me/submissions/c1ad4836-07e9-4668-b018-e85a0f2b7a27

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_6_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow6_e_oai : ∀ j : Fin 27, Z 6 j =
    ∑ k, lowerUnit entries k 6 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_6_0_e
  · exact entry_6_1_e
  · exact entry_6_2_e
  · exact entry_6_3_e
  · exact entry_6_4_e
  · exact entry_6_5_e
  · exact entry_6_6_e
  · exact entry_6_7_e
  · exact entry_6_8_e
  · exact entry_6_9_e
  · exact entry_6_10_e
  · exact entry_6_11_e
  · exact entry_6_12_e
  · exact entry_6_13_e
  · exact entry_6_14_e
  · exact entry_6_15_e
  · exact entry_6_16_e
  · exact entry_6_17_e
  · exact entry_6_18_e
  · exact entry_6_19_e
  · exact entry_6_20_e
  · exact entry_6_21_e
  · exact entry_6_22_e
  · exact entry_6_23_e
  · exact entry_6_24_e
  · exact entry_6_25_e
  · exact entry_6_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow6_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow6_e_oai
