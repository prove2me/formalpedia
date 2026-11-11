-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow19_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:39.587786+00:00
-- url     : https://prove2.me/submissions/30217619-6c16-4e2b-846d-1be4f3ec4cab

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_19_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow19_e_oai : ∀ j : Fin 27, Z 19 j =
    ∑ k, lowerUnit entries k 19 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_19_0_e
  · exact entry_19_1_e
  · exact entry_19_2_e
  · exact entry_19_3_e
  · exact entry_19_4_e
  · exact entry_19_5_e
  · exact entry_19_6_e
  · exact entry_19_7_e
  · exact entry_19_8_e
  · exact entry_19_9_e
  · exact entry_19_10_e
  · exact entry_19_11_e
  · exact entry_19_12_e
  · exact entry_19_13_e
  · exact entry_19_14_e
  · exact entry_19_15_e
  · exact entry_19_16_e
  · exact entry_19_17_e
  · exact entry_19_18_e
  · exact entry_19_19_e
  · exact entry_19_20_e
  · exact entry_19_21_e
  · exact entry_19_22_e
  · exact entry_19_23_e
  · exact entry_19_24_e
  · exact entry_19_25_e
  · exact entry_19_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow19_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow19_e_oai
