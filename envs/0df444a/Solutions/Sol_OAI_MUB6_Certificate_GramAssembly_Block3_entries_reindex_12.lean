-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex_12
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T18:35:01.499053+00:00
-- url     : https://prove2.me/submissions/4fe3f2d8-bfa2-41d8-8f22-5cae37663b42

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D199

open OAI OAI.MUB6.Certificate OAI.MUB6.Certificate.GramAssembly OAI.MUB6.Certificate.GramAssembly.Block3 in
theorem solution (j : Fin 27) :
    Integer.Sparse.reindex key (entries 12 j) = GramEntries.Block3.entries 12 j := by
  revert j
  decide +kernel
