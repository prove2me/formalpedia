-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_1
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T18:34:48.299021+00:00
-- url     : https://prove2.me/submissions/f140b13f-96e0-46e9-be42-58470a3d2bff

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D199

open OAI OAI.MUB6.Certificate OAI.MUB6.Certificate.GramAssembly OAI.MUB6.Certificate.GramAssembly.Block3 in
theorem solution (j : Fin 27) :
    Integer.Sparse.reindex key (entries 1 j) = GramEntries.Block3.entries 1 j := by
  revert j
  decide +kernel
