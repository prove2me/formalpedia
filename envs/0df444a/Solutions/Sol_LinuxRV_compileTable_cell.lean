-- Prove2me | solution 1 for LinuxRV.compileTable_cell
-- status  : ACCEPTED   (prove)
-- author  : @jdenwood
-- created : 2026-11-23T08:55:34.17081+00:00
-- url     : https://prove2.me/submissions/9239ff4c-6c89-4308-bf48-5e55674059d3

import Definitions.Def_LinuxRV_TransitionTable
open RamadgeWonham.Shared

open LinuxRV in
theorem solution {α : Type} {n m : Nat} (G : Generator α)
    (states : G.Q ≃ Fin n) (events : α ≃ Fin m) (q : G.Q) (e : α) :
    (compileTable G states events)[states q][events e] = encodeNext states (G.δ e q) := by
  simp [compileTable]
