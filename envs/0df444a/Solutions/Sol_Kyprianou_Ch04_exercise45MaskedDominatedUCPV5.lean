-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45MaskedDominatedUCPV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T20:38:08.102066+00:00
-- url     : https://prove2.me/submissions/d61a0ac9-e332-455b-9323-d6c40a4544b3

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise45DyadicDominatedUCPV5
import Theorems.Thm_Kyprianou_Ch04_exercise45MaskedLimitRegularV5
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- An arbitrary possibly nonmeasurable error has vanishing outer probability when a regular approximation and residual dominate it. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (U A R : ℕ → NNReal → Ω → ℝ) (J : NNReal → Ω → ℝ) (T : NNReal)
    (hm : ∀ n t, AEMeasurable (A n t) P ∧ AEMeasurable (R n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t,
      ContinuousWithinAt (fun s => A n s w) (Ici t) t ∧
      ContinuousWithinAt (fun s => R n s w) (Ici t) t)
    (hu : ∀ᵐ w ∂P, ∀ L : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ L, |A n t w - J t w| < δ)
    (hR : ∀ᵐ w ∂P, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |R n t w| < δ)
    (hb : ∀ᵐ w ∂P, ∀ n t, t ≤ T →
      |U n t w| ≤ |A n t w - J t w| + |R n t w|)
    (δ : ℝ) (hδ : 0 < δ) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, δ ≤ |U n t w|}).toReal) atTop (nhds 0) := by
  have hA : ∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => A n s w) (Ici t) t := by
    filter_upwards [hr] with w hw
    exact fun n t => (hw n t).1
  obtain ⟨hmJ,hrJ⟩ := Kyprianou.Ch04.exercise45MaskedLimitRegularV5 P A J
    (fun n t => (hm n t).1) hA hu
  let V n t w := |A n t w - J t w| + |R n t w|
  apply Kyprianou.Ch04.exercise45DyadicDominatedUCPV5 P U V T _ _ _ _ δ hδ
  · intro n t
    exact (((hm n t).1.sub (hmJ t)).abs).add (hm n t).2.abs
  · filter_upwards [hr,hrJ] with w hw hj
    exact fun n t => (((hw n t).1.sub (hj t)).abs).add (hw n t).2.abs
  · filter_upwards [hb] with w hw n t ht
    exact (hw n t ht).trans (le_abs_self _)
  · filter_upwards [hu,hR] with w hw hwr
    intro e he
    obtain ⟨N,hN⟩ := hw T (e/2) (by positivity)
    obtain ⟨M,hM⟩ := hwr (e/2) (by positivity)
    refine ⟨max N M,fun n hn t ht => ?_⟩
    have h1 := hN n ((le_max_left N M).trans hn) t ht
    have h2 := hM n ((le_max_right N M).trans hn) t ht
    rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    change |A n t w - J t w| + |R n t w| < e
    linarith
