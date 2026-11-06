-- Prove2me | solution 1 for Monodromy.FormalCompilation.eval1
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:35:12.292452+00:00
-- url     : https://prove2.me/submissions/3bc24e2d-967d-427b-96b9-da8da220ab2a

import Definitions.Def_Monodromy_FormalCompilation
import Mathlib.Computability.StateTransition
import Mathlib.Computability.TuringMachine.ToPartrec

open Monodromy
open Monodromy.FormalCompilation
open Turing

namespace Monodromy.FormalCompilation

variable (source : ToPartrec.Code)

theorem initial_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.init source values)
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) := by
  let _ : Inhabited Label2 := ⟨PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt⟩
  have initial := TM2to1.trCfg_init (Γ := fun _ : Stack => Symbol) (Λ := Label2) (σ := Store)
    PartrecToTM2.K'.main (PartrecToTM2.trList values)
  have same : (TM2.init PartrecToTM2.K'.main (PartrecToTM2.trList values) :
      TM2.Cfg (fun _ : Stack => Symbol) Label2 Store) = PartrecToTM2.init source values := by
    apply congrArg (fun storage => TM2.Cfg.mk
      (some (PartrecToTM2.trNormal source PartrecToTM2.Cont'.halt)) none storage)
    funext index
    cases index <;> rfl
  rw [same] at initial
  exact initial

/-- Projection to every stack determines the entire packed tape. -/
theorem relation_unique
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {first second : TM1.Cfg Alphabet (Control1 source) Store}
    (first_related : TM2to1.TrCfg configuration first)
    (second_related : TM2to1.TrCfg configuration second) : first = second := by
  cases first_related with
  | mk first first_projection =>
      cases second_related with
      | mk second second_projection =>
          have same : first = second := by
            apply ListBlank.ext
            intro index
            funext column
            have projected := congrArg (fun word => ListBlank.nth word index)
              ((first_projection column).trans (second_projection column).symm)
            simpa only [proj_map_nth] using projected
          subst second
          rfl

theorem relation_stop
    {configuration : TM2.Cfg (fun _ : Stack => Symbol) Label2 Store}
    {target : TM1.Cfg Alphabet (Control1 source) Store}
    (related : TM2to1.TrCfg configuration target) :
    TM2to1.TrCfg (Λ := Label2) { configuration with l := none } { target with l := none } := by
  cases related with
  | mk contents projection => exact TM2to1.TrCfg.mk contents projection

theorem halt_relation (values : List ℕ) :
    TM2to1.TrCfg (PartrecToTM2.halt values) (halt1 source values) :=
  relation_stop source (initial_relation source values)

end Monodromy.FormalCompilation

/-- The complete result, including divergence, survives stack-to-tape translation. -/
theorem solution (source : ToPartrec.Code) (values : List ℕ) :
    StateTransition.eval (TM1.step (machine1 source))
      (TM1.init (tapeData values) : TM1.Cfg Alphabet (Control1 source) Store) =
      halt1 source <$> source.eval values := by
  have source_evaluation := PartrecToTM2.tr_eval source values
  apply Part.ext
  intro target
  constructor
  · intro completed
    obtain ⟨source_result, related, finished⟩ := StateTransition.tr_eval_rev
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) completed
    rw [source_evaluation] at finished
    obtain ⟨value, value_finished, rfl⟩ := (Part.mem_map_iff _).mp finished
    exact (Part.mem_map_iff _).mpr
      ⟨value, value_finished, (relation_unique source related (halt_relation source value)).symm⟩
  · intro completed
    obtain ⟨result, result_finished, rfl⟩ := (Part.mem_map_iff _).mp completed
    have source_finished : PartrecToTM2.halt result ∈
        StateTransition.eval (TM2.step PartrecToTM2.tr) (PartrecToTM2.init source values) := by
      rw [source_evaluation]
      exact (Part.mem_map_iff _).mpr ⟨result, result_finished, rfl⟩
    obtain ⟨target, related, finished⟩ := StateTransition.tr_eval
      (TM2to1.tr_respects PartrecToTM2.tr) (initial_relation source values) source_finished
    have same := relation_unique source related (halt_relation source result)
    rw [same] at finished
    exact finished
