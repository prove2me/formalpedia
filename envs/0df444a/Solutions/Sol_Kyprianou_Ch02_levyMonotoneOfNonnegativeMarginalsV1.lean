-- Prove2me | solution 1 for Kyprianou.Ch02.levyMonotoneOfNonnegativeMarginalsV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:35:51.51466+00:00
-- url     : https://prove2.me/submissions/1268e509-f3e0-4248-810d-3ff1ac4e4915

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent

import Theorems.Thm_Kyprianou_Ch02_levyNonnegativeMarginalOrderedIncrementV1
import Theorems.Thm_Kyprianou_Ch02_cadlagMonotoneOfDenseSequenceV1
open MeasureTheory ProbabilityTheory Complex
open scoped NNReal ENNReal
set_option autoImplicit false
open Filter Topology Set

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P) :
    (∀ t : ℝ≥0, ∀ᵐ ω ∂P, 0 ≤ X t ω) →
    (∀ᵐ ω ∂P, Monotone (fun t : ℝ≥0 => X t ω)) := by
  intro hm
  obtain ⟨ts, hdense⟩ := TopologicalSpace.exists_dense_seq ℝ≥0
  have hsched : ∀ᵐ ω ∂P, ∀ i j : ℕ, ts i ≤ ts j → X (ts i) ω ≤ X (ts j) ω := by
    simp only [ae_all_iff]
    intro i j
    intro hij
    exact Kyprianou.Ch02.levyNonnegativeMarginalOrderedIncrementV1
      P X hX hm (ts i) (ts j) hij
  filter_upwards [hsched, hX.cadlag_ae] with ω hω hc
  intro s t hst
  rcases eq_or_lt_of_le hst with heq | hlt
  · subst t
    exact le_rfl
  · exact Kyprianou.Ch02.cadlagMonotoneOfDenseSequenceV1
      (fun u => X u ω) hc ts hdense hω s t hlt
