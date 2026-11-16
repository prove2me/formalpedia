-- Prove2me | solution 1 for Kyprianou.Ch06.strictGridIndependentIncrements
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:11:58.338509+00:00
-- url     : https://prove2.me/submissions/25f13304-500e-4619-bc92-de4371030659

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
import Theorems.Thm_Kyprianou_Ch06_iIndepFunOfFullRectangle

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- Strict increasing time grids in Chapter 6 have independent increments in
the published stochastic-process API. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hprob : P Set.univ = 1)
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i})
    (n : Nat) (times : Fin (n + 1) → NNReal)
    (hstrict : StrictMono times) :
    ProbabilityTheory.iIndepFun
      (fun i : Fin n =>
        ProbabilityTheory.increment X (times i.castSucc) (times i.succ)) P := by
  apply Kyprianou.Ch06.iIndepFunOfFullRectangle P hprob n
  intro A hA
  exact hindep n times hstrict A hA
