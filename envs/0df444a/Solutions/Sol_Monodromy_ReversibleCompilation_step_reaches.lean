-- Prove2me | solution 1 for Monodromy.ReversibleCompilation.step_reaches
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T23:18:10.203513+00:00
-- url     : https://prove2.me/submissions/45438576-4c6f-4ac0-84f2-e86459b49984
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

module
public import Definitions.Def_Monodromy_Counter
public import Theorems.Thm_Monodromy_Counter_Reversible_step_iff
public import Theorems.Thm_Monodromy_StagedProgram_cycle_ofFn
public import Theorems.Thm_Monodromy_StagedProgram_cycle_reaches
public import Theorems.Thm_Monodromy_ReversibleCompilation_cycle_step

@[expose] public section

open Monodromy
open Monodromy.ReversibleCompilation
open Counter.Reversible CoupledContinuation
variable {q e : ℕ} [NeZero q]

private lemma haltMark_source_local (table : Table 2 q e) (position : Fin q) :
    haltMark table (Fin.castAdd e position) =
      decide (¬ ∃ edge, (table edge).source = position) := by
  simp [haltMark]

theorem solution (table : Table 2 q e) (deterministic : Deterministic table)
    (compatible : TargetCompatible table) {first last : State 2 q}
    (transition : Counter.Reversible.step table first = some last) :
    StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
      (iota (e := e) first) (iota (e := e) last) := by
  obtain ⟨edge, enabled, _⟩ := (Counter.Reversible.step_iff table deterministic).mp transition
  have outgoing : ∃ edge, (table edge).source = first.1 := ⟨edge, enabled.1⟩
  have unmarked : haltMark table (Fin.castAdd e first.1) = false := by
    simp [haltMark_source_local, outgoing]
  have run := StagedProgram.cycle_reaches 11 (q + e)
    (stages table deterministic compatible) (haltMark table)
    (first.2 0) (first.2 1) 0 (Fin.castAdd e first.1) unmarked
  have ending :
      StagedProgram.embed 11 0
        ((List.ofFn (stages table deterministic compatible)).foldl
          (fun point stage => stage.advance point) (sourcePoint (e := e) first)) =
      iota (e := e) last :=
    (StagedProgram.cycle_ofFn 11 (q + e) (stages table deterministic compatible)
      (sourcePoint (e := e) first)).symm.trans
      (cycle_step table deterministic compatible transition)
  have actual :
      StateTransition.Reaches₁ (haltingProgram table deterministic compatible).step
        (iota (e := e) first)
        (StagedProgram.embed 11 0
          ((List.ofFn (stages table deterministic compatible)).foldl
            (fun point stage => stage.advance point) (sourcePoint (e := e) first))) := by
    simpa only [haltingProgram, iota, sourcePoint, point, mul_zero, zero_add] using run
  rw [ending] at actual
  exact actual
