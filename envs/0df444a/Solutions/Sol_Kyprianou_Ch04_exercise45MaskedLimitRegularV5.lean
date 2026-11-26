-- Prove2me | solution 1 for Kyprianou.Ch04.exercise45MaskedLimitRegularV5
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:38:18.421101+00:00
-- url     : https://prove2.me/submissions/470312e4-0cac-418d-873b-813ca3c683ad

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false
/-- Measurable right-continuous approximants give a measurable right-continuous compact uniform limit. -/
theorem solution {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (A : ℕ → NNReal → Ω → ℝ) (J : NNReal → Ω → ℝ)
    (hm : ∀ n t, AEMeasurable (A n t) P)
    (hr : ∀ᵐ w ∂P, ∀ n t, ContinuousWithinAt (fun s => A n s w) (Ici t) t)
    (hu : ∀ᵐ w ∂P, ∀ T : NNReal, ∀ δ : ℝ, 0 < δ →
      ∃ N : ℕ, ∀ n ≥ N, ∀ t ≤ T, |A n t w - J t w| < δ) :
    (∀ t, AEMeasurable (J t) P) ∧
      (∀ᵐ w ∂P, ∀ t, ContinuousWithinAt (fun s => J s w) (Ici t) t) := by
  constructor
  · intro t
    apply aemeasurable_of_tendsto_metrizable_ae atTop (fun n => hm n t)
    filter_upwards [hu] with w hw
    apply Metric.tendsto_nhds.mpr
    intro δ hd
    obtain ⟨N,hN⟩ := hw t δ hd
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [Real.dist_eq]
    exact hN n hn t le_rfl
  · filter_upwards [hr,hu] with w hwr hwu
    intro t
    apply Metric.tendsto_nhds.mpr
    intro δ hd
    obtain ⟨N,hN⟩ := hwu (t+1) (δ/3) (by positivity)
    have hc := Metric.tendsto_nhds.mp (hwr N t) (δ/3) (by positivity)
    have ht : ∀ᶠ s in nhdsWithin t (Ici t), s < t+1 :=
      nhdsWithin_le_nhds (Iio_mem_nhds (by simp))
    filter_upwards [hc,ht] with s hs hst
    rw [Real.dist_eq] at hs ⊢
    have ha := hN N le_rfl s hst.le
    have hb := hN N le_rfl t (by simp)
    calc
      |J s w - J t w| =
          |(J s w - A N s w) + (A N s w - A N t w) + (A N t w - J t w)| := by ring_nf
      _ ≤ |(J s w - A N s w) + (A N s w - A N t w)| + |A N t w - J t w| :=
        abs_add_le _ _
      _ ≤ |J s w - A N s w| + |A N s w - A N t w| + |A N t w - J t w| :=
        add_le_add_left (abs_add_le _ _) _
      _ < δ := by rw [abs_sub_comm (J s w) (A N s w)]; linarith
