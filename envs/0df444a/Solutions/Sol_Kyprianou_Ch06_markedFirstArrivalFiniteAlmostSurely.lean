-- Prove2me | solution 1 for Kyprianou.Ch06.markedFirstArrivalFiniteAlmostSurely
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:51:06.660201+00:00
-- url     : https://prove2.me/submissions/9ba46462-0a2a-4c50-af2a-1bbd95cee86c

import Mathlib
import Definitions.Def_Kyprianou_Ch06_MarkedPoissonPointProcess
import Theorems.Thm_Kyprianou_Ch06_markedPoissonArrivalSurvival
import Theorems.Thm_Kyprianou_Ch06_exponentialSurvivalFiniteAlmostSurely
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Omega E : Type} [MeasurableSpace Omega] [MeasurableSpace E]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (n : Measure E) (N : Omega → NNReal → Set E → Nat)
    (A : Set E) (firstMark : Omega → Option E)
    (hPPP : Kyprianou.Ch06.IsMarkedPoissonPointProcess P n N)
    (hA : MeasurableSet A)
    (hFinite : n A < ⊤) (hPositive : 0 < n A)
    (hMark : ∀ᵐ omega ∂P,
      let sigma : WithTop NNReal :=
        sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
          {t : NNReal | 0 < t ∧ 0 < N omega t A})
      (sigma = ⊤ → firstMark omega = none) ∧
      (sigma ≠ ⊤ → ∃ x : E,
        firstMark omega = some x ∧ x ∈ A ∧
        0 < N omega (sigma.untopD 0) {x})) :
    P {omega |
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}) = ⊤} = 0 := by
  have hSurv :=
    Kyprianou.Ch06.markedPoissonArrivalSurvival
      P n N A firstMark hPPP hA hFinite hMark
  dsimp only at hSurv
  have hRate : 0 < (n A).toReal :=
    ENNReal.toReal_pos hPositive.ne' (ne_of_lt hFinite)
  exact Kyprianou.Ch06.exponentialSurvivalFiniteAlmostSurely
    P
    (fun omega =>
      sInf ((fun t : NNReal => (t : WithTop NNReal)) ''
        {t : NNReal | 0 < t ∧ 0 < N omega t A}))
    (n A).toReal hRate hSurv
