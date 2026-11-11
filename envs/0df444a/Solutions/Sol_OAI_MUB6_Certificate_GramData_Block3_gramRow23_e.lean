-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow23_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:21.487315+00:00
-- url     : https://prove2.me/submissions/4377f40d-4592-42fe-8781-17eaf89a9a28

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_23_26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gramRow23_e_oai : ∀ j : Fin 27, Z 23 j =
    ∑ k, lowerUnit entries k 23 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_23_0_e
  · exact entry_23_1_e
  · exact entry_23_2_e
  · exact entry_23_3_e
  · exact entry_23_4_e
  · exact entry_23_5_e
  · exact entry_23_6_e
  · exact entry_23_7_e
  · exact entry_23_8_e
  · exact entry_23_9_e
  · exact entry_23_10_e
  · exact entry_23_11_e
  · exact entry_23_12_e
  · exact entry_23_13_e
  · exact entry_23_14_e
  · exact entry_23_15_e
  · exact entry_23_16_e
  · exact entry_23_17_e
  · exact entry_23_18_e
  · exact entry_23_19_e
  · exact entry_23_20_e
  · exact entry_23_21_e
  · exact entry_23_22_e
  · exact entry_23_23_e
  · exact entry_23_24_e
  · exact entry_23_25_e
  · exact entry_23_26_e

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow23_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow23_e_oai
