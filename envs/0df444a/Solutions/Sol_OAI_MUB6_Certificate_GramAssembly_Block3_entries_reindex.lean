-- Prove2me | solution 1 for OAI.MUB6.Certificate.GramAssembly.Block3.entries_reindex
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-11-02T18:36:05.879747+00:00
-- url     : https://prove2.me/submissions/d1411e08-4a3e-4f8e-a5bc-46d73cb5459e

import Mathlib
import Lean.Elab.Tactic.Omega
import Definitions.Def_OAIQ106D199

open OAI OAI.MUB6.Certificate OAI.MUB6.Certificate.GramAssembly OAI.MUB6.Certificate.GramAssembly.Block3 in
theorem solution (i j : Fin 27) :
    Integer.Sparse.reindex key (entries i j) = GramEntries.Block3.entries i j := by
  revert i j
  decide +kernel
