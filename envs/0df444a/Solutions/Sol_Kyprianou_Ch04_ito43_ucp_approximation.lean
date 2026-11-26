-- Prove2me | solution 1 for Kyprianou.Ch04.ito43_ucp_approximation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T15:56:08.829605+00:00
-- url     : https://prove2.me/submissions/2a470ccb-1156-4013-b7cb-d4ce027f4585

import Mathlib
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

/-- Uniform-in-probability convergence follows from convergent truncations and vanishing tails. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (E : ℕ → NNReal → Ω → ℝ) (A B : ℕ → ℕ → NNReal → Ω → ℝ) (T : NNReal)
    (hE : ∀ m n t w, E n t w = A m n t w + B m n t w)
    (hAl : ∀ (m : ℕ) (e : ℝ), 0 < e → Tendsto
      (fun n => (P {w | ∃ t ≤ T, e ≤ |A m n t w|}).toReal) atTop (nhds 0))
    (hB : ∀ e : ℝ, 0 < e → ∀ η : ℝ, 0 < η → ∃ m : ℕ,
      ∀ᶠ n in atTop, (P {w | ∃ t ≤ T, e ≤ |B m n t w|}).toReal ≤ η)
    (e : ℝ) (he : 0 < e) :
    Tendsto (fun n => (P {w | ∃ t ≤ T, e ≤ |E n t w|}).toReal) atTop (nhds 0) := by
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨m,hm⟩ := hB (e/2) (by positivity) (η/3) (by positivity)
  obtain ⟨N1,hN1⟩ := Metric.tendsto_atTop.mp (hAl m (e/2) (by positivity)) (η/3) (by positivity)
  obtain ⟨N2,hN2⟩ := eventually_atTop.mp hm
  refine ⟨max N1 N2,?_⟩
  intro n hn
  let U : Set Ω := {w | ∃ t ≤ T, e/2 ≤ |A m n t w|}
  let V : Set Ω := {w | ∃ t ≤ T, e/2 ≤ |B m n t w|}
  let W : Set Ω := {w | ∃ t ≤ T, e ≤ |E n t w|}
  have hsub : W ⊆ U ∪ V := by
    rintro w ⟨t,ht,hw⟩
    rw [hE m n t w] at hw
    by_cases h : e/2 ≤ |A m n t w|
    · exact Or.inl ⟨t,ht,h⟩
    · exact Or.inr ⟨t,ht,by linarith [abs_add_le (A m n t w) (B m n t w),lt_of_not_ge h]⟩
  have hUV : (P W).toReal ≤ (P U).toReal + (P V).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top P U) (measure_ne_top P V)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨measure_ne_top P U,measure_ne_top P V⟩)
      ((measure_mono hsub).trans (measure_union_le U V))
  have hu := hN1 n ((le_max_left _ _).trans hn)
  have hv := hN2 n ((le_max_right _ _).trans hn)
  change dist (P W).toReal 0 < η
  change dist (P U).toReal 0 < η/3 at hu
  change (P V).toReal ≤ η/3 at hv
  simp only [Real.dist_eq,sub_zero,abs_of_nonneg ENNReal.toReal_nonneg] at hu ⊢
  linarith
