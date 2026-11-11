-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow15_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:47.599024+00:00
-- url     : https://prove2.me/submissions/75550f33-8c30-4a76-a820-ea1a7996a4cc

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_15_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow15_e_oai : ∀ j : Fin 27, Z 15 j =
    ∑ k, lowerUnit entries k 15 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_15_0_e
  · exact entry_15_1_e
  · exact entry_15_2_e
  · exact entry_15_3_e
  · exact entry_15_4_e
  · exact entry_15_5_e
  · exact entry_15_6_e
  · exact entry_15_7_e
  · exact entry_15_8_e
  · exact entry_15_9_e
  · exact entry_15_10_e
  · exact entry_15_11_e
  · exact entry_15_12_e
  · exact entry_15_13_e
  · exact entry_15_14_e
  · exact entry_15_15_e
  · exact entry_15_16_e
  · exact entry_15_17_e
  · exact entry_15_18_e
  · exact entry_15_19_e
  · exact entry_15_20_e
  · exact entry_15_21_e
  · exact entry_15_22_e
  · exact entry_15_23_e
  · exact entry_15_24_e
  · exact entry_15_25_e
  · exact entry_15_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow15_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow15_e_oai
