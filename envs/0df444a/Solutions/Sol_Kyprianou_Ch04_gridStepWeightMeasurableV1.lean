-- Prove2me | solution 1 for Kyprianou.Ch04.gridStepWeightMeasurableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:52:32.831657+00:00
-- url     : https://prove2.me/submissions/340380b1-7868-4725-9343-0ec27c764cff

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
import Definitions.Def_Kyprianou_Ch04_Exercise4_5CertificationV3
import Theorems.Thm_Kyprianou_Ch04_gridStepPredictableSumV1
open MeasureTheory Filter Set Topology LevyStochCalc.Poisson
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The step interpolation with predictable cell coefficients is measurable on the predictable sigma field. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance) (u : ℕ → NNReal) (n : ℕ)
    (H : ℕ → Ω → ℝ) (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k)) :
    Measurable[F.predictable] (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k p.2) p.1) := by
  have he : (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1))).indicator
        (fun _ => H k p.2) p.1) = (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n, (Ioc (u k) (u (k+1)) ×ˢ (univ : Set Ω)).indicator
        (fun q : NNReal × Ω => H k q.2) p) := by
    funext p
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hs : p.1 ∈ Ioc (u k) (u (k+1)) <;> simp [Set.indicator_apply,hs]
  rw [he]
  exact Kyprianou.Ch04.gridStepPredictableSumV1 F n u H hH
