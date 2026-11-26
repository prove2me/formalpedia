-- Prove2me | solution 1 for MorreySubadditive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:07:37.261422+00:00
-- url     : https://prove2.me/submissions/c1338fad-5aea-4adc-bd29-669a27ef39fb

import Definitions.Def_Tablet_morreyNorm
import Definitions.Def_Tablet_MorreySubadditive

set_option autoImplicit false
open MeasureTheory Set
theorem _root_.solution {E : Type*} [MetricSpace E] [MeasurableSpace E]
    {ι : Type*} (s : Finset ι) (μ : ι → Measure E) :
    morreyNorm (∑ i ∈ s, μ i) ≤ ∑ i ∈ s, morreyNorm (μ i) := by
-- BODY
  classical
  have binary : ∀ ν₁ ν₂ : Measure E, morreyNorm (ν₁ + ν₂) ≤ morreyNorm ν₁ + morreyNorm ν₂ := by
    intro ν₁ ν₂
    unfold morreyNorm
    refine iSup_le fun x => iSup_le fun r => iSup_le fun hr => ?_
    have hsum : (ν₁ + ν₂) (Metric.closedBall x r) =
        ν₁ (Metric.closedBall x r) + ν₂ (Metric.closedBall x r) := rfl
    rw [hsum, ENNReal.add_div]
    refine add_le_add ?_ ?_
    · exact le_iSup₂_of_le x r (le_iSup_of_le hr le_rfl)
    · exact le_iSup₂_of_le x r (le_iSup_of_le hr le_rfl)
  induction s using Finset.induction with
  | empty => simp [morreyNorm]
  | insert a t ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (binary (μ a) (∑ i ∈ t, μ i)).trans (add_le_add le_rfl ih)
