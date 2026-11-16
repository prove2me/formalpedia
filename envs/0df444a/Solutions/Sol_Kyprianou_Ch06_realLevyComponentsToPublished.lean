-- Prove2me | solution 1 for Kyprianou.Ch06.realLevyComponentsToPublished
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:46:18.858983+00:00
-- url     : https://prove2.me/submissions/01ba8124-7111-46aa-8ddc-46cc5988dc6f

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch06_probabilityFromIncrementCylinderLaw
import Theorems.Thm_Kyprianou_Ch06_weakGridIndependentIncrements
import Theorems.Thm_Kyprianou_Ch06_levyProcessOfWeakGridIndependence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

/-- Every original Chapter 6 Lévy-process source assumption yields the
published LeanLevy process interface for the almost-surely equal, exactly
zero-initialised normalisation of the process. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) (X : NNReal → Ω → Real)
    (hmeas : ∀ t : NNReal, Measurable (X t))
    (hzero : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ s t : NNReal,
      P.map (fun ω => X (s + t) ω - X s ω) = P.map (X t))
    (hindep : ∀ (n : Nat) (times : Fin (n + 1) → NNReal),
      StrictMono times →
      ∀ A : Fin n → Set Real, (∀ i, MeasurableSet (A i)) →
        P {ω | ∀ i : Fin n,
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i} =
        ∏ i : Fin n, P {ω |
          X (times i.succ) ω - X (times i.castSucc) ω ∈ A i})
    (hregular : ∀ᵐ ω ∂P, ∀ t : NNReal,
      ContinuousWithinAt (fun u : NNReal => X u ω) (Set.Ici t) t ∧
      (t = 0 ∨ ∃ x : Real,
        Tendsto (fun u : NNReal => X u ω)
          (nhdsWithin t (Set.Iio t)) (nhds x))) :
    ProbabilityTheory.IsLevyProcess
      (fun t ω => if t = 0 then (0 : Real) else X t ω) P := by
  have hprob : P Set.univ = 1 :=
    Kyprianou.Ch06.probabilityFromIncrementCylinderLaw P X hindep
  have hweak : ProbabilityTheory.HasIndependentIncrements X P :=
    Kyprianou.Ch06.weakGridIndependentIncrements P X hprob hindep
  exact Kyprianou.Ch06.levyProcessOfWeakGridIndependence
    P X hmeas hzero hlaw hweak hregular
