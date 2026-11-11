-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow21_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:17.965195+00:00
-- url     : https://prove2.me/submissions/228b6e6d-c556-48d3-9e1b-2297d1e68edc

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_21_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow21_e_oai : ∀ j : Fin 27, Z 21 j =
    ∑ k, lowerUnit entries k 21 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_21_0_e
  · exact entry_21_1_e
  · exact entry_21_2_e
  · exact entry_21_3_e
  · exact entry_21_4_e
  · exact entry_21_5_e
  · exact entry_21_6_e
  · exact entry_21_7_e
  · exact entry_21_8_e
  · exact entry_21_9_e
  · exact entry_21_10_e
  · exact entry_21_11_e
  · exact entry_21_12_e
  · exact entry_21_13_e
  · exact entry_21_14_e
  · exact entry_21_15_e
  · exact entry_21_16_e
  · exact entry_21_17_e
  · exact entry_21_18_e
  · exact entry_21_19_e
  · exact entry_21_20_e
  · exact entry_21_21_e
  · exact entry_21_22_e
  · exact entry_21_23_e
  · exact entry_21_24_e
  · exact entry_21_25_e
  · exact entry_21_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow21_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow21_e_oai
