-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_6_e
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-10T09:44:07.587221+00:00
-- url     : https://prove2.me/submissions/8f4bf3f9-faad-42a1-9f19-dae365520af3

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106E007
import Definitions.Def_OAIQ106E032
import Definitions.Def_OAIQ106E043

section
-- module Solutions.OAIQ106_MUB.MutuallyUnbiased_GramAssembly_Block4Reindex6
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

namespace MUB6.Certificate.GramAssembly.Block4

theorem entry_reindex_6_0 :
    Integer.Sparse.reindex key entry_6_0 = GramEntries.Block4.entries 6 0 := by
  decide +kernel

theorem entry_reindex_6_1 :
    Integer.Sparse.reindex key entry_6_1 = GramEntries.Block4.entries 6 1 := by
  decide +kernel

theorem entry_reindex_6_2 :
    Integer.Sparse.reindex key entry_6_2 = GramEntries.Block4.entries 6 2 := by
  decide +kernel

theorem entry_reindex_6_3 :
    Integer.Sparse.reindex key entry_6_3 = GramEntries.Block4.entries 6 3 := by
  decide +kernel

theorem entry_reindex_6_4 :
    Integer.Sparse.reindex key entry_6_4 = GramEntries.Block4.entries 6 4 := by
  decide +kernel

theorem entry_reindex_6_5 :
    Integer.Sparse.reindex key entry_6_5 = GramEntries.Block4.entries 6 5 := by
  decide +kernel

theorem entry_reindex_6_6 :
    Integer.Sparse.reindex key entry_6_6 = GramEntries.Block4.entries 6 6 := by
  decide +kernel

theorem entry_reindex_6_7 :
    Integer.Sparse.reindex key entry_6_7 = GramEntries.Block4.entries 6 7 := by
  decide +kernel

theorem entry_reindex_6_8 :
    Integer.Sparse.reindex key entry_6_8 = GramEntries.Block4.entries 6 8 := by
  decide +kernel

theorem entry_reindex_6_9 :
    Integer.Sparse.reindex key entry_6_9 = GramEntries.Block4.entries 6 9 := by
  decide +kernel

theorem entry_reindex_6_10 :
    Integer.Sparse.reindex key entry_6_10 = GramEntries.Block4.entries 6 10 := by
  decide +kernel

theorem entry_reindex_6_11 :
    Integer.Sparse.reindex key entry_6_11 = GramEntries.Block4.entries 6 11 := by
  decide +kernel

theorem entry_reindex_6_12 :
    Integer.Sparse.reindex key entry_6_12 = GramEntries.Block4.entries 6 12 := by
  decide +kernel

theorem entry_reindex_6_13 :
    Integer.Sparse.reindex key entry_6_13 = GramEntries.Block4.entries 6 13 := by
  decide +kernel

theorem entry_reindex_6_14 :
    Integer.Sparse.reindex key entry_6_14 = GramEntries.Block4.entries 6 14 := by
  decide +kernel

theorem entry_reindex_6_15 :
    Integer.Sparse.reindex key entry_6_15 = GramEntries.Block4.entries 6 15 := by
  decide +kernel

theorem entry_reindex_6_16 :
    Integer.Sparse.reindex key entry_6_16 = GramEntries.Block4.entries 6 16 := by
  decide +kernel

theorem entry_reindex_6_17 :
    Integer.Sparse.reindex key entry_6_17 = GramEntries.Block4.entries 6 17 := by
  decide +kernel

theorem entry_reindex_6_18 :
    Integer.Sparse.reindex key entry_6_18 = GramEntries.Block4.entries 6 18 := by
  decide +kernel

theorem entry_reindex_6_19 :
    Integer.Sparse.reindex key entry_6_19 = GramEntries.Block4.entries 6 19 := by
  decide +kernel

theorem entry_reindex_6_20 :
    Integer.Sparse.reindex key entry_6_20 = GramEntries.Block4.entries 6 20 := by
  decide +kernel

theorem entry_reindex_6_21 :
    Integer.Sparse.reindex key entry_6_21 = GramEntries.Block4.entries 6 21 := by
  decide +kernel

theorem entries_reindex_6_e_oai (j : Fin 22) :
    Integer.Sparse.reindex key (entries 6 j) = GramEntries.Block4.entries 6 j := by
  fin_cases j
  · exact entry_reindex_6_0
  · exact entry_reindex_6_1
  · exact entry_reindex_6_2
  · exact entry_reindex_6_3
  · exact entry_reindex_6_4
  · exact entry_reindex_6_5
  · exact entry_reindex_6_6
  · exact entry_reindex_6_7
  · exact entry_reindex_6_8
  · exact entry_reindex_6_9
  · exact entry_reindex_6_10
  · exact entry_reindex_6_11
  · exact entry_reindex_6_12
  · exact entry_reindex_6_13
  · exact entry_reindex_6_14
  · exact entry_reindex_6_15
  · exact entry_reindex_6_16
  · exact entry_reindex_6_17
  · exact entry_reindex_6_18
  · exact entry_reindex_6_19
  · exact entry_reindex_6_20
  · exact entry_reindex_6_21

end MUB6.Certificate.GramAssembly.Block4

end OAI
end

theorem solution : type_of% @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_6_e_oai := @OAI.MUB6.Certificate.GramAssembly.Block4.entries_reindex_6_e_oai
