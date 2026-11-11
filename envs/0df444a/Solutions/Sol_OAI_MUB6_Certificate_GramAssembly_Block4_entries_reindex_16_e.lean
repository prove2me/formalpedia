-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_16_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:44:06.344568+00:00
-- url     : https://prove2.me/submissions/a47bf10f-ca06-452f-920e-88049b426227

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Reindex16
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_16_0 :
    Integer.Sparse.reindex key entry_16_0 = GramEntries.Block4.entries 16 0 := by
  decide +kernel

theorem entry_reindex_16_1 :
    Integer.Sparse.reindex key entry_16_1 = GramEntries.Block4.entries 16 1 := by
  decide +kernel

theorem entry_reindex_16_2 :
    Integer.Sparse.reindex key entry_16_2 = GramEntries.Block4.entries 16 2 := by
  decide +kernel

theorem entry_reindex_16_3 :
    Integer.Sparse.reindex key entry_16_3 = GramEntries.Block4.entries 16 3 := by
  decide +kernel

theorem entry_reindex_16_4 :
    Integer.Sparse.reindex key entry_16_4 = GramEntries.Block4.entries 16 4 := by
  decide +kernel

theorem entry_reindex_16_5 :
    Integer.Sparse.reindex key entry_16_5 = GramEntries.Block4.entries 16 5 := by
  decide +kernel

theorem entry_reindex_16_6 :
    Integer.Sparse.reindex key entry_16_6 = GramEntries.Block4.entries 16 6 := by
  decide +kernel

theorem entry_reindex_16_7 :
    Integer.Sparse.reindex key entry_16_7 = GramEntries.Block4.entries 16 7 := by
  decide +kernel

theorem entry_reindex_16_8 :
    Integer.Sparse.reindex key entry_16_8 = GramEntries.Block4.entries 16 8 := by
  decide +kernel

theorem entry_reindex_16_9 :
    Integer.Sparse.reindex key entry_16_9 = GramEntries.Block4.entries 16 9 := by
  decide +kernel

theorem entry_reindex_16_10 :
    Integer.Sparse.reindex key entry_16_10 = GramEntries.Block4.entries 16 10 := by
  decide +kernel

theorem entry_reindex_16_11 :
    Integer.Sparse.reindex key entry_16_11 = GramEntries.Block4.entries 16 11 := by
  decide +kernel

theorem entry_reindex_16_12 :
    Integer.Sparse.reindex key entry_16_12 = GramEntries.Block4.entries 16 12 := by
  decide +kernel

theorem entry_reindex_16_13 :
    Integer.Sparse.reindex key entry_16_13 = GramEntries.Block4.entries 16 13 := by
  decide +kernel

theorem entry_reindex_16_14 :
    Integer.Sparse.reindex key entry_16_14 = GramEntries.Block4.entries 16 14 := by
  decide +kernel

theorem entry_reindex_16_15 :
    Integer.Sparse.reindex key entry_16_15 = GramEntries.Block4.entries 16 15 := by
  decide +kernel

theorem entry_reindex_16_16 :
    Integer.Sparse.reindex key entry_16_16 = GramEntries.Block4.entries 16 16 := by
  decide +kernel

theorem entry_reindex_16_17 :
    Integer.Sparse.reindex key entry_16_17 = GramEntries.Block4.entries 16 17 := by
  decide +kernel

theorem entry_reindex_16_18 :
    Integer.Sparse.reindex key entry_16_18 = GramEntries.Block4.entries 16 18 := by
  decide +kernel

theorem entry_reindex_16_19 :
    Integer.Sparse.reindex key entry_16_19 = GramEntries.Block4.entries 16 19 := by
  decide +kernel

theorem entry_reindex_16_20 :
    Integer.Sparse.reindex key entry_16_20 = GramEntries.Block4.entries 16 20 := by
  decide +kernel

theorem entry_reindex_16_21 :
    Integer.Sparse.reindex key entry_16_21 = GramEntries.Block4.entries 16 21 := by
  decide +kernel

theorem entries_reindex_16_e_oai (j : Fin 22) :
    Integer.Sparse.reindex key (entries 16 j) = GramEntries.Block4.entries 16 j := by
  fin_cases j
  · exact entry_reindex_16_0
  · exact entry_reindex_16_1
  · exact entry_reindex_16_2
  · exact entry_reindex_16_3
  · exact entry_reindex_16_4
  · exact entry_reindex_16_5
  · exact entry_reindex_16_6
  · exact entry_reindex_16_7
  · exact entry_reindex_16_8
  · exact entry_reindex_16_9
  · exact entry_reindex_16_10
  · exact entry_reindex_16_11
  · exact entry_reindex_16_12
  · exact entry_reindex_16_13
  · exact entry_reindex_16_14
  · exact entry_reindex_16_15
  · exact entry_reindex_16_16
  · exact entry_reindex_16_17
  · exact entry_reindex_16_18
  · exact entry_reindex_16_19
  · exact entry_reindex_16_20
  · exact entry_reindex_16_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_16_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_16_e_oai
