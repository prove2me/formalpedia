-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow9_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:44.225205+00:00
-- url     : https://prove2.me/submissions/4890ce66-7c13-4c1a-8a50-b22b38c41262

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_9_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow9_e_oai : ∀ j : Fin 27, Z 9 j =
    ∑ k, lowerUnit entries k 9 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_9_0_e
  · exact entry_9_1_e
  · exact entry_9_2_e
  · exact entry_9_3_e
  · exact entry_9_4_e
  · exact entry_9_5_e
  · exact entry_9_6_e
  · exact entry_9_7_e
  · exact entry_9_8_e
  · exact entry_9_9_e
  · exact entry_9_10_e
  · exact entry_9_11_e
  · exact entry_9_12_e
  · exact entry_9_13_e
  · exact entry_9_14_e
  · exact entry_9_15_e
  · exact entry_9_16_e
  · exact entry_9_17_e
  · exact entry_9_18_e
  · exact entry_9_19_e
  · exact entry_9_20_e
  · exact entry_9_21_e
  · exact entry_9_22_e
  · exact entry_9_23_e
  · exact entry_9_24_e
  · exact entry_9_25_e
  · exact entry_9_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow9_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow9_e_oai
