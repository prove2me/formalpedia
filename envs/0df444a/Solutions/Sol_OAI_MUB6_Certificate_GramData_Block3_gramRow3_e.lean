-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow3_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:37.241068+00:00
-- url     : https://prove2.me/submissions/b53b1b98-e508-4b7d-8dd0-57e644179d67

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_3_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow3_e_oai : ∀ j : Fin 27, Z 3 j =
    ∑ k, lowerUnit entries k 3 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_3_0_e
  · exact entry_3_1_e
  · exact entry_3_2_e
  · exact entry_3_3_e
  · exact entry_3_4_e
  · exact entry_3_5_e
  · exact entry_3_6_e
  · exact entry_3_7_e
  · exact entry_3_8_e
  · exact entry_3_9_e
  · exact entry_3_10_e
  · exact entry_3_11_e
  · exact entry_3_12_e
  · exact entry_3_13_e
  · exact entry_3_14_e
  · exact entry_3_15_e
  · exact entry_3_16_e
  · exact entry_3_17_e
  · exact entry_3_18_e
  · exact entry_3_19_e
  · exact entry_3_20_e
  · exact entry_3_21_e
  · exact entry_3_22_e
  · exact entry_3_23_e
  · exact entry_3_24_e
  · exact entry_3_25_e
  · exact entry_3_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow3_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow3_e_oai
