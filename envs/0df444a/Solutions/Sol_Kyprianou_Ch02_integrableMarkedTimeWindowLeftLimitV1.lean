-- Prove2me | solution 1 for Kyprianou.Ch02.integrableMarkedTimeWindowLeftLimitV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T22:58:43.944848+00:00
-- url     : https://prove2.me/submissions/8d2385b2-7c41-4a7c-af84-7667b7461ffc

import Mathlib
open MeasureTheory Filter
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ × ℝ)) (B : Set ℝ) (hB : MeasurableSet B)
    (g : ℝ × ℝ → ℝ) (hg : Integrable g μ) (t : ℝ≥0) :
    Tendsto (fun s : ℝ≥0 => ∫ z in (Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B), g z ∂μ)
      (nhdsWithin t (Set.Iio t))
      (nhds (∫ z in (Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B), g z ∂μ))  := by
  let A (s : ℝ≥0) : Set (ℝ × ℝ) := Set.Ioc (0 : ℝ) (s : ℝ) ×ˢ B
  let L : Set (ℝ × ℝ) := Set.Ioo (0 : ℝ) (t : ℝ) ×ˢ B
  let F (s : ℝ≥0) := (A s).indicator g
  let l := nhdsWithin t (Set.Iio t)
  have hA (s : ℝ≥0) : MeasurableSet (A s) := measurableSet_Ioc.prod hB
  have hL : MeasurableSet L := measurableSet_Ioo.prod hB
  have hnear : ∀ᶠ s in l, s ∈ Set.Iio t := self_mem_nhdsWithin
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) l (nhds (t : ℝ)) :=
    (NNReal.continuous_coe.tendsto t).mono_left nhdsWithin_le_nhds
  have hpoint (z : ℝ × ℝ) : Tendsto (fun s => F s z) l (nhds (L.indicator g z)) := by
    by_cases hz : z ∈ L
    · have hmem : ∀ᶠ (s : ℝ≥0) in l, z.1 < (s : ℝ) :=
        hcoe.eventually (Ioi_mem_nhds hz.1.2)
      apply tendsto_const_nhds.congr'
      filter_upwards [hmem] with s hs
      have h : z ∈ A s := ⟨⟨hz.1.1, hs.le⟩, hz.2⟩
      simp only [F, Set.indicator_of_mem h, Set.indicator_of_mem hz]
    · apply tendsto_const_nhds.congr'
      filter_upwards [hnear] with s hs
      have hst : (s : ℝ) < (t : ℝ) := by
        change s < t at hs
        exact_mod_cast hs
      have h : z ∉ A s := fun h => hz ⟨⟨h.1.1, h.1.2.trans_lt hst⟩, h.2⟩
      simp only [F, Set.indicator_of_notMem h, Set.indicator_of_notMem hz]
  have hm (s : ℝ≥0) : AEStronglyMeasurable (F s) μ :=
    hg.aestronglyMeasurable.indicator (hA s)
  have hb (s : ℝ≥0) (z : ℝ × ℝ) : ‖F s z‖ ≤ ‖g z‖ := by
    by_cases hz : z ∈ A s
    · simp only [F, Set.indicator_of_mem hz, le_refl]
    · simp only [F, Set.indicator_of_notMem hz, norm_zero, norm_nonneg]
  have hconv := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (l := l) (fun z => ‖g z‖)
    (Eventually.of_forall hm)
    (Eventually.of_forall fun s => Eventually.of_forall (hb s))
    hg.norm (Eventually.of_forall hpoint)
  simpa only [F, integral_indicator, hA, hL, A, L, l] using hconv
