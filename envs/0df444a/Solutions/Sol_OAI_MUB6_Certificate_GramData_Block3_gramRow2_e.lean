-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow2_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:46.51974+00:00
-- url     : https://prove2.me/submissions/24466fd5-6224-4646-bb75-6b6707bae000

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_2_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow2_e_oai : ∀ j : Fin 27, Z 2 j =
    ∑ k, lowerUnit entries k 2 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_2_0_e
  · exact entry_2_1_e
  · exact entry_2_2_e
  · exact entry_2_3_e
  · exact entry_2_4_e
  · exact entry_2_5_e
  · exact entry_2_6_e
  · exact entry_2_7_e
  · exact entry_2_8_e
  · exact entry_2_9_e
  · exact entry_2_10_e
  · exact entry_2_11_e
  · exact entry_2_12_e
  · exact entry_2_13_e
  · exact entry_2_14_e
  · exact entry_2_15_e
  · exact entry_2_16_e
  · exact entry_2_17_e
  · exact entry_2_18_e
  · exact entry_2_19_e
  · exact entry_2_20_e
  · exact entry_2_21_e
  · exact entry_2_22_e
  · exact entry_2_23_e
  · exact entry_2_24_e
  · exact entry_2_25_e
  · exact entry_2_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow2_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow2_e_oai
