-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow14_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:43.997617+00:00
-- url     : https://prove2.me/submissions/036fb298-b4ec-4d97-88b7-4066b6bcf688

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_14_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow14_e_oai : ∀ j : Fin 27, Z 14 j =
    ∑ k, lowerUnit entries k 14 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_14_0_e
  · exact entry_14_1_e
  · exact entry_14_2_e
  · exact entry_14_3_e
  · exact entry_14_4_e
  · exact entry_14_5_e
  · exact entry_14_6_e
  · exact entry_14_7_e
  · exact entry_14_8_e
  · exact entry_14_9_e
  · exact entry_14_10_e
  · exact entry_14_11_e
  · exact entry_14_12_e
  · exact entry_14_13_e
  · exact entry_14_14_e
  · exact entry_14_15_e
  · exact entry_14_16_e
  · exact entry_14_17_e
  · exact entry_14_18_e
  · exact entry_14_19_e
  · exact entry_14_20_e
  · exact entry_14_21_e
  · exact entry_14_22_e
  · exact entry_14_23_e
  · exact entry_14_24_e
  · exact entry_14_25_e
  · exact entry_14_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow14_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow14_e_oai
