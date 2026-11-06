-- Prove2me | solution 1 for Monodromy.ReversibleNativeTuring.step_firstReturn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:15:09.336588+00:00
-- url     : https://prove2.me/submissions/d632d5a3-1121-4d2e-83d5-d4c443100dc3
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

module
public import Definitions.Def_Monodromy_FormalCompilation
public import Theorems.Thm_Monodromy_ReversibleCompilation_marked_firstReturn
public import Theorems.Thm_Monodromy_ReversibleTuring_Compression_step_firstReturn

@[expose] public section

open Monodromy
open Monodromy.ReversibleNativeTuring
open Turing CoupledContinuation ReversibleTuring
variable (a q : ℕ) [NeZero a] [NeZero q]

theorem solution (machine : TM0.Machine (Fin a) (Fin q))
    {first last : TM0.Cfg (Fin a) (Fin q)} (transition : TM0.step machine first = some last)
    (history : ℕ) :
    ∃ finalHistory, history < finalHistory ∧
      FirstReturn a q machine (iota a q machine first history) (iota a q machine last finalHistory) := by
  obtain ⟨finalHistory, grew, first_marked, last_marked, middle, initial, rest⟩ :=
    Compression.step_firstReturn a q machine transition history
  have marked_iff (state : Counter.Reversible.State 2 (Compression.size a q machine)) :
      Compression.mark a q machine state.1 = true ↔ Compression.Boundary a q machine state := by
    change decide (Compression.Boundary a q machine (state.1, fun _ => 0)) = true ↔
      Compression.Boundary a q machine (state.1, fun _ => 0)
    exact ⟨of_decide_eq_true, decide_eq_true⟩
  have unmarked_iff (state : Counter.Reversible.State 2 (Compression.size a q machine)) :
      Compression.mark a q machine state.1 = false ↔ ¬ Compression.Boundary a q machine state := by
    rw [← marked_iff state]
    cases Compression.mark a q machine state.1 <;> decide
  have inside : Relation.ReflTransGen
      (fun current next : Counter.Reversible.State 2 (Compression.size a q machine) =>
        Counter.Reversible.step (Compression.table a q machine) current = some next ∧
          Compression.mark a q machine current.1 = false)
      middle (Compression.encode a q machine last finalHistory) :=
    Relation.ReflTransGen.mono
      (fun current _ edge => ⟨edge.1, (unmarked_iff current).mpr edge.2⟩)
      _ _ rest
  exact ⟨finalHistory, grew, ReversibleCompilation.marked_firstReturn (Compression.table a q machine)
    (Compression.deterministic a q machine) (Compression.targetCompatible a q machine)
    (Compression.mark a q machine) initial inside
    ((marked_iff _).mpr first_marked)
    ((marked_iff _).mpr last_marked)⟩
