-- Prove2me | solution 1 for Monodromy.CoupledContinuation.execute_B_left_zero
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:25:17.416364+00:00
-- url     : https://prove2.me/submissions/59fd00de-9597-498c-ae1e-f2c2f7946e8c

import Definitions.Def_Monodromy_Continuation

open Monodromy
open Monodromy.CoupledContinuation

theorem solution (state : Memory) (zero : state.val.1.1.val = 1) :
    (execute B_left state).val.2 = state.val.2 + NestedContinuation.period 1 := by
  obtain ⟨⟨⟨left, right⟩, control⟩, rfl⟩ := prepare_surjective state
  change NestedContinuation.firstRoot left = 1 at zero
  have left_zero : left = 0 := NestedContinuation.firstRoot_injective (by
    simpa [NestedContinuation.firstRoot, NestedContinuation.period] using zero)
  rw [execute_B_left, left_zero]
  change upperRoot 0 right (control + 1) = upperRoot 0 right control +
    NestedContinuation.period 1
  simp only [upperRoot, NestedContinuation.period]
  push_cast
  ring
