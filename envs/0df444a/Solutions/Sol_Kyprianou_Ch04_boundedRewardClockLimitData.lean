-- Prove2me | solution 1 for Kyprianou.Ch04.boundedRewardClockLimitData
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T00:49:59.954419+00:00
-- url     : https://prove2.me/submissions/8e859aa9-fe29-47bf-93f1-497d47d033a9

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_antitoneRewardMeanProperties
import Theorems.Thm_Kyprianou_Ch04_clockMeanLimit
import Theorems.Thm_Kyprianou_Ch04_boundedClockProductAverage
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Both deterministic and exponential-clock means approach the same limit. -/
theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (g : NNReal × Ω → ℝ) (hg : Measurable g)
    (hg0 : ∀ z, 0 ≤ g z) (hg1 : ∀ z, g z ≤ 1)
    (hga : ∀ w, Antitone (fun t : NNReal => g (t,w)))
    (q : ℕ → ℝ) (hq : ∀ n, 0 < q n)
    (herr : ∀ T : NNReal, Tendsto (fun n => 1 - Real.exp (-(q n * (T : ℝ)))) atTop (nhds 0)) :
    ∃ ell : ℝ,
      Tendsto (fun t : NNReal => ∫ w, g (t,w) ∂P) atTop (nhds ell) ∧
      Tendsto (fun n : ℕ => ∫ z : Ω × ℝ, g (z.2.toNNReal,z.1) ∂(P.prod (expMeasure (q n)))) atTop (nhds ell) := by
  obtain ⟨hf,hfa,hf0,hf1,ell,hlo,hlim⟩ :=
    Kyprianou.Ch04.antitoneRewardMeanProperties P g hg hg0 hg1 hga
  refine ⟨ell,hlim,?_⟩
  have hA := Kyprianou.Ch04.clockMeanLimit _ hf hfa hf0 hf1 ell hlo hlim q hq herr
  apply hA.congr'
  exact Eventually.of_forall fun n => by
    let : IsProbabilityMeasure (expMeasure (q n)) := isProbabilityMeasure_expMeasure (hq n)
    exact (Kyprianou.Ch04.boundedClockProductAverage P (expMeasure (q n)) g hg hg0 hg1).symm
