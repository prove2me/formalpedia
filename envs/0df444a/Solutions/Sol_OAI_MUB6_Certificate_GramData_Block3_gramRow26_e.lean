-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramData.Block3.gramRow26_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T14:24:03.794597+00:00
-- url     : https://prove2.me/submissions/b8cd779d-588b-4715-918f-f00b1cca4e9d

import Mathlib
import Definitions.Def_OAIQ106E002
import Definitions.Def_OAIQ106E147
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_10_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_11_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_12_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_13_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_14_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_15_e
import Theorems.Thm_OAI_MUB6_Certificate_GramData_Block3_entry_26_16_e

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramData.Block3

open Matrix
open scoped BigOperators

theorem entry_26_0 : Z 26 0 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 0 := by
  decide +kernel

theorem entry_26_1 : Z 26 1 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 1 := by
  decide +kernel

theorem entry_26_2 : Z 26 2 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 2 := by
  decide +kernel

theorem entry_26_3 : Z 26 3 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 3 := by
  decide +kernel

theorem entry_26_4 : Z 26 4 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 4 := by
  decide +kernel

theorem entry_26_5 : Z 26 5 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 5 := by
  decide +kernel

theorem entry_26_6 : Z 26 6 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 6 := by
  decide +kernel

theorem entry_26_7 : Z 26 7 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 7 := by
  decide +kernel

theorem entry_26_8 : Z 26 8 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 8 := by
  decide +kernel

theorem entry_26_9 : Z 26 9 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 9 := by
  decide +kernel

theorem entry_26_17 : Z 26 17 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 17 := by
  decide +kernel

theorem entry_26_18 : Z 26 18 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 18 := by
  decide +kernel

theorem entry_26_19 : Z 26 19 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 19 := by
  decide +kernel

theorem entry_26_20 : Z 26 20 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 20 := by
  decide +kernel

theorem entry_26_21 : Z 26 21 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 21 := by
  decide +kernel

theorem entry_26_22 : Z 26 22 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 22 := by
  decide +kernel

theorem entry_26_23 : Z 26 23 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 23 := by
  decide +kernel

theorem entry_26_24 : Z 26 24 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 24 := by
  decide +kernel

theorem entry_26_25 : Z 26 25 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 25 := by
  decide +kernel

theorem entry_26_26 : Z 26 26 =
    ∑ k : Fin 27, lowerUnit entries k 26 * D k * lowerUnit entries k 26 := by
  decide +kernel

theorem gramRow26_e_oai : ∀ j : Fin 27, Z 26 j =
    ∑ k, lowerUnit entries k 26 * D k * lowerUnit entries k j := by
  intro j
  fin_cases j
  · exact entry_26_0
  · exact entry_26_1
  · exact entry_26_2
  · exact entry_26_3
  · exact entry_26_4
  · exact entry_26_5
  · exact entry_26_6
  · exact entry_26_7
  · exact entry_26_8
  · exact entry_26_9
  · exact entry_26_10_e
  · exact entry_26_11_e
  · exact entry_26_12_e
  · exact entry_26_13_e
  · exact entry_26_14_e
  · exact entry_26_15_e
  · exact entry_26_16_e
  · exact entry_26_17
  · exact entry_26_18
  · exact entry_26_19
  · exact entry_26_20
  · exact entry_26_21
  · exact entry_26_22
  · exact entry_26_23
  · exact entry_26_24
  · exact entry_26_25
  · exact entry_26_26

end MUB6.Certificate.GramData.Block3

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramData.Block3.gramRow26_e_oai := @OAI.MUB6.Certificate.GramData.Block3.gramRow26_e_oai
