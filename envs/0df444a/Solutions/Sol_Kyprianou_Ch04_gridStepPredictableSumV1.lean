-- Prove2me | solution 1 for Kyprianou.Ch04.gridStepPredictableSumV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T23:00:16.946726+00:00
-- url     : https://prove2.me/submissions/895a0b7b-b19c-43cc-a7e6-aa7e96aa7dab

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_predictableGridCellV1
open MeasureTheory Filter Set
open scoped NNReal
set_option autoImplicit false

/-- Finite sums of past-measurable right-closed cell coefficients are predictable. -/
theorem solution {Ω : Type} [MeasurableSpace Ω]
    (F : Filtration NNReal inferInstance)
    (n : ℕ) (u : ℕ → NNReal) (H : ℕ → Ω → ℝ)
    (hH : ∀ k ∈ Finset.range n, Measurable[F (u k)] (H k)) :
    Measurable[F.predictable] (fun p : NNReal × Ω =>
      ∑ k ∈ Finset.range n,
        (Ioc (u k) (u (k+1)) ×ˢ (univ : Set Ω)).indicator
          (fun q : NNReal × Ω => H k q.2) p) := by
  letI : MeasurableSpace (NNReal × Ω) := F.predictable
  exact Finset.measurable_sum _ (fun k hk =>
    Kyprianou.Ch04.predictableGridCellV1 F (u k) (u (k+1)) (H k) (hH k hk))
