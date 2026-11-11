-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow17_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:31.971948+00:00
-- url     : https://prove2.me/submissions/ff4c82aa-4c0d-4139-9dbd-0ca0ed8a46e2

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_17_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow17_e_oai : ∀ j : Fin 27, Z 17 j =
    ∑ k, lowerUnit entries k 17 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_17_0_e
  · exact entry_17_1_e
  · exact entry_17_2_e
  · exact entry_17_3_e
  · exact entry_17_4_e
  · exact entry_17_5_e
  · exact entry_17_6_e
  · exact entry_17_7_e
  · exact entry_17_8_e
  · exact entry_17_9_e
  · exact entry_17_10_e
  · exact entry_17_11_e
  · exact entry_17_12_e
  · exact entry_17_13_e
  · exact entry_17_14_e
  · exact entry_17_15_e
  · exact entry_17_16_e
  · exact entry_17_17_e
  · exact entry_17_18_e
  · exact entry_17_19_e
  · exact entry_17_20_e
  · exact entry_17_21_e
  · exact entry_17_22_e
  · exact entry_17_23_e
  · exact entry_17_24_e
  · exact entry_17_25_e
  · exact entry_17_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow17_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow17_e_oai
