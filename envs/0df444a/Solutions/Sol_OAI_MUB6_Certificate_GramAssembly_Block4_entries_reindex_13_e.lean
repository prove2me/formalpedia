-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:44:42.560212+00:00
-- url     : https://prove2.me/submissions/cefdf560-0e1b-40f6-96f3-6ae30367eaef

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Reindex13
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_13_0 :
    Integer.Sparse.reindex key entry_13_0 = GramEntries.Block4.entries 13 0 := by
  decide +kernel

theorem entry_reindex_13_1 :
    Integer.Sparse.reindex key entry_13_1 = GramEntries.Block4.entries 13 1 := by
  decide +kernel

theorem entry_reindex_13_2 :
    Integer.Sparse.reindex key entry_13_2 = GramEntries.Block4.entries 13 2 := by
  decide +kernel

theorem entry_reindex_13_3 :
    Integer.Sparse.reindex key entry_13_3 = GramEntries.Block4.entries 13 3 := by
  decide +kernel

theorem entry_reindex_13_4 :
    Integer.Sparse.reindex key entry_13_4 = GramEntries.Block4.entries 13 4 := by
  decide +kernel

theorem entry_reindex_13_5 :
    Integer.Sparse.reindex key entry_13_5 = GramEntries.Block4.entries 13 5 := by
  decide +kernel

theorem entry_reindex_13_6 :
    Integer.Sparse.reindex key entry_13_6 = GramEntries.Block4.entries 13 6 := by
  decide +kernel

theorem entry_reindex_13_7 :
    Integer.Sparse.reindex key entry_13_7 = GramEntries.Block4.entries 13 7 := by
  decide +kernel

theorem entry_reindex_13_8 :
    Integer.Sparse.reindex key entry_13_8 = GramEntries.Block4.entries 13 8 := by
  decide +kernel

theorem entry_reindex_13_9 :
    Integer.Sparse.reindex key entry_13_9 = GramEntries.Block4.entries 13 9 := by
  decide +kernel

theorem entry_reindex_13_10 :
    Integer.Sparse.reindex key entry_13_10 = GramEntries.Block4.entries 13 10 := by
  decide +kernel

theorem entry_reindex_13_11 :
    Integer.Sparse.reindex key entry_13_11 = GramEntries.Block4.entries 13 11 := by
  decide +kernel

theorem entry_reindex_13_12 :
    Integer.Sparse.reindex key entry_13_12 = GramEntries.Block4.entries 13 12 := by
  decide +kernel

theorem entry_reindex_13_13 :
    Integer.Sparse.reindex key entry_13_13 = GramEntries.Block4.entries 13 13 := by
  decide +kernel

theorem entry_reindex_13_14 :
    Integer.Sparse.reindex key entry_13_14 = GramEntries.Block4.entries 13 14 := by
  decide +kernel

theorem entry_reindex_13_15 :
    Integer.Sparse.reindex key entry_13_15 = GramEntries.Block4.entries 13 15 := by
  decide +kernel

theorem entry_reindex_13_16 :
    Integer.Sparse.reindex key entry_13_16 = GramEntries.Block4.entries 13 16 := by
  decide +kernel

theorem entry_reindex_13_17 :
    Integer.Sparse.reindex key entry_13_17 = GramEntries.Block4.entries 13 17 := by
  decide +kernel

theorem entry_reindex_13_18 :
    Integer.Sparse.reindex key entry_13_18 = GramEntries.Block4.entries 13 18 := by
  decide +kernel

theorem entry_reindex_13_19 :
    Integer.Sparse.reindex key entry_13_19 = GramEntries.Block4.entries 13 19 := by
  decide +kernel

theorem entry_reindex_13_20 :
    Integer.Sparse.reindex key entry_13_20 = GramEntries.Block4.entries 13 20 := by
  decide +kernel

theorem entry_reindex_13_21 :
    Integer.Sparse.reindex key entry_13_21 = GramEntries.Block4.entries 13 21 := by
  decide +kernel

theorem entries_reindex_13_e_oai (j : Fin 22) :
    Integer.Sparse.reindex key (entries 13 j) = GramEntries.Block4.entries 13 j := by
  fin_cases j
  · exact entry_reindex_13_0
  · exact entry_reindex_13_1
  · exact entry_reindex_13_2
  · exact entry_reindex_13_3
  · exact entry_reindex_13_4
  · exact entry_reindex_13_5
  · exact entry_reindex_13_6
  · exact entry_reindex_13_7
  · exact entry_reindex_13_8
  · exact entry_reindex_13_9
  · exact entry_reindex_13_10
  · exact entry_reindex_13_11
  · exact entry_reindex_13_12
  · exact entry_reindex_13_13
  · exact entry_reindex_13_14
  · exact entry_reindex_13_15
  · exact entry_reindex_13_16
  · exact entry_reindex_13_17
  · exact entry_reindex_13_18
  · exact entry_reindex_13_19
  · exact entry_reindex_13_20
  · exact entry_reindex_13_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_13_e_oai
