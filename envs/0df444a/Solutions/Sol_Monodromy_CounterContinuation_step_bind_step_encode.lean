-- Prove2me | solution 1 for Monodromy.CounterContinuation.step_bind_step_encode
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:03:11.521206+00:00
-- url     : https://prove2.me/submissions/cb53bf5e-fc95-4da5-aae2-9a91602f93cd

module
public import Definitions.Def_Monodromy_Counter
public import Theorems.Thm_Monodromy_CounterContinuation_simulates
public import Theorems.Thm_Monodromy_CounterContinuation_two_returns

@[expose] public section

open Monodromy
open Monodromy.CounterContinuation
open CoupledContinuation
variable {m : ℕ} [NeZero m]

theorem solution (program : Counter.Program 2 m) (state : Counter.Configuration 2 m) :
    ((compile program).step (encode state)).bind (compile program).step =
      (Counter.step program state).map encode := by
  cases source_step : Counter.step program state with
  | none =>
      have native_halt : (compile program).step (encode state) = none := by
        have respects : StateTransition.FRespects (compile program).step encode
            (encode state) (Counter.step program state) :=
          StateTransition.fun_respects.mp (simulates program) (a₁ := state)
        rw [source_step] at respects
        exact respects
      simp [source_step, native_halt]
  | some result =>
      obtain ⟨middle, first_return, second_return⟩ :=
        two_returns program state result source_step
      simp [source_step, first_return, second_return]
