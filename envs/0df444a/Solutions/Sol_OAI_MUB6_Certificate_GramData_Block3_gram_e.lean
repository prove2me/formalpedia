-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gram_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:22.820979+00:00
-- url     : https://prove2.me/submissions/61f478d1-5725-4c6c-a346-a3b9d8a9c41c

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow0_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow1_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow2_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow3_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow4_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow5_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow6_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow7_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow8_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow9_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow16_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow17_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow18_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow19_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow20_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow21_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow22_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow23_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow24_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow25_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_gramRow26_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem gram_e_oai : ∀ i j : Fin 27, Z i j =
    ∑ k, lowerUnit entries k i * D k * lowerUnit entries k j := by
  intro i j
  fin_cases i
  · exact gramRow0_e j
  · exact gramRow1_e j
  · exact gramRow2_e j
  · exact gramRow3_e j
  · exact gramRow4_e j
  · exact gramRow5_e j
  · exact gramRow6_e j
  · exact gramRow7_e j
  · exact gramRow8_e j
  · exact gramRow9_e j
  · exact gramRow10_e j
  · exact gramRow11_e j
  · exact gramRow12_e j
  · exact gramRow13_e j
  · exact gramRow14_e j
  · exact gramRow15_e j
  · exact gramRow16_e j
  · exact gramRow17_e j
  · exact gramRow18_e j
  · exact gramRow19_e j
  · exact gramRow20_e j
  · exact gramRow21_e j
  · exact gramRow22_e j
  · exact gramRow23_e j
  · exact gramRow24_e j
  · exact gramRow25_e j
  · exact gramRow26_e j

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gram_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gram_e_oai
