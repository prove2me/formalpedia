-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow11_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:37.068983+00:00
-- url     : https://prove2.me/submissions/eb9297ae-18d0-4a44-96ff-555545847f5e

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_11_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow11_e_oai : ∀ j : Fin 27, Z 11 j =
    ∑ k, lowerUnit entries k 11 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_11_0_e
  · exact entry_11_1_e
  · exact entry_11_2_e
  · exact entry_11_3_e
  · exact entry_11_4_e
  · exact entry_11_5_e
  · exact entry_11_6_e
  · exact entry_11_7_e
  · exact entry_11_8_e
  · exact entry_11_9_e
  · exact entry_11_10_e
  · exact entry_11_11_e
  · exact entry_11_12_e
  · exact entry_11_13_e
  · exact entry_11_14_e
  · exact entry_11_15_e
  · exact entry_11_16_e
  · exact entry_11_17_e
  · exact entry_11_18_e
  · exact entry_11_19_e
  · exact entry_11_20_e
  · exact entry_11_21_e
  · exact entry_11_22_e
  · exact entry_11_23_e
  · exact entry_11_24_e
  · exact entry_11_25_e
  · exact entry_11_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow11_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow11_e_oai
