-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow10_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:44.214403+00:00
-- url     : https://prove2.me/submissions/274ccb71-f535-464e-9bc9-a0a623951e51

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_10_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow10_e_oai : ∀ j : Fin 27, Z 10 j =
    ∑ k, lowerUnit entries k 10 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_10_0_e
  · exact entry_10_1_e
  · exact entry_10_2_e
  · exact entry_10_3_e
  · exact entry_10_4_e
  · exact entry_10_5_e
  · exact entry_10_6_e
  · exact entry_10_7_e
  · exact entry_10_8_e
  · exact entry_10_9_e
  · exact entry_10_10_e
  · exact entry_10_11_e
  · exact entry_10_12_e
  · exact entry_10_13_e
  · exact entry_10_14_e
  · exact entry_10_15_e
  · exact entry_10_16_e
  · exact entry_10_17_e
  · exact entry_10_18_e
  · exact entry_10_19_e
  · exact entry_10_20_e
  · exact entry_10_21_e
  · exact entry_10_22_e
  · exact entry_10_23_e
  · exact entry_10_24_e
  · exact entry_10_25_e
  · exact entry_10_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow10_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow10_e_oai
