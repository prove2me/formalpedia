-- Prove2me | solution 1 for Kyprianou.Ch04.physicalRetainedMarkDCTV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T17:21:16.380353+00:00
-- url     : https://prove2.me/submissions/47af69f7-bb21-439d-bc29-3bb7fecfdd1f

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- A varying retained-mark cutoff preserves integrals under a common integrable envelope. -/
theorem solution (R : Measure (ℝ × ℝ)) (T : NNReal)
    (J : ℕ → ℝ × ℝ → ℝ) (G : ℝ × ℝ → ℝ)
    (e : ℕ → ℝ) (B : ℝ × ℝ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hJ : ∀ n, Measurable (J n))
    (hB : IntegrableOn B (Icc (0 : ℝ) (T : ℝ) ×ˢ univ) R)
    (hdom : ∀ n z, z ∈ Icc (0 : ℝ) (T : ℝ) ×ˢ univ → |J n z| ≤ B z)
    (hz : ∀ n s, J n (s,0) = 0) (hGz : ∀ s, G (s,0) = 0)
    (hconv : ∀ᵐ z ∂ R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ univ),
      z.2 ≠ 0 → Tendsto (fun n => J n z) atTop (𝓝 (G z))) :
    Tendsto (fun n => ∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e n < |x|}, J n z ∂ R)
      atTop (𝓝 (∫ z in Icc (0 : ℝ) (T : ℝ) ×ˢ univ, G z ∂ R)) := by
  let A := Icc (0 : ℝ) (T : ℝ) ×ˢ (univ : Set ℝ)
  let C (n : ℕ) := {z : ℝ × ℝ | e n < |z.2|}
  have hC (n : ℕ) : MeasurableSet (C n) := measurableSet_lt measurable_const measurable_snd.abs
  have hm (n : ℕ) : Measurable ((C n).indicator (J n)) :=
    (hJ n).indicator (hC n)
  have hEq (n : ℕ) :
      R.restrict (Icc (0 : ℝ) (T : ℝ) ×ˢ {x : ℝ | e n < |x|}) =
        (R.restrict A).restrict (C n) := by
    rw [Measure.restrict_restrict (hC n)]
    congr 1
    ext z
    simp [A,C,and_comm]
  have hDom (n : ℕ) : ∀ᵐ z ∂ R.restrict A, ‖(C n).indicator (J n) z‖ ≤ B z := by
    filter_upwards [ae_restrict_mem (μ := R) (show MeasurableSet A from
      measurableSet_Icc.prod MeasurableSet.univ)] with z hz'
    by_cases h : z ∈ C n
    · simpa [Set.indicator_of_mem h,Real.norm_eq_abs] using hdom n z hz'
    · rw [Set.indicator_of_notMem h,norm_zero]
      exact (abs_nonneg _).trans (hdom n z hz')
  have hLim : ∀ᵐ z ∂ R.restrict A,
      Tendsto (fun n => (C n).indicator (J n) z) atTop (𝓝 (G z)) := by
    filter_upwards [hconv] with z h
    by_cases h0 : z.2 = 0
    · have heq (n : ℕ) : (C n).indicator (J n) z = 0 := by
        have hJz : J n z = 0 := by
          obtain ⟨s,x⟩ := z
          simp only at h0
          subst x
          exact hz n s
        simp [Set.indicator_apply,hJz]
      have hG : G z = 0 := by
        obtain ⟨s,x⟩ := z
        simp only at h0
        subst x
        exact hGz s
      simp only [heq,hG]
      exact tendsto_const_nhds
    · apply (h h0).congr'
      filter_upwards [(tendsto_order.mp he).2 |z.2| (abs_pos.mpr h0)] with n hn
      exact (Set.indicator_of_mem (show z ∈ C n from hn) (J n)).symm
  have h := tendsto_integral_of_dominated_convergence B
    (fun n => (hm n).aestronglyMeasurable) hB hDom hLim
  apply h.congr'
  filter_upwards [] with n
  rw [integral_indicator (hC n), ← hEq n]
