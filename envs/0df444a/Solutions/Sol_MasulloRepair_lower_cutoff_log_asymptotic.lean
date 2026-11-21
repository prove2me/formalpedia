-- Prove2me | solution 1 for MasulloRepair.lower_cutoff_log_asymptotic
-- status  : ACCEPTED   (prove)
-- author  : @dga471
-- created : 2026-11-21T02:13:44.714216+00:00
-- url     : https://prove2.me/submissions/9b1874ed-0e31-440f-af35-507ea9678abf

import Mathlib

open MeasureTheory Filter Topology

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) (q : Ω → ℝ) (H : Ω → ℂ)
    (hq : Measurable q) (hqpos : ∀ᵐ w ∂ν, 0 < q w)
    (hH : Integrable H ν)
    (hHlog : Integrable (fun w => H w * (Real.log (q w) : ℂ)) ν) :
    Tendsto
      (fun p : ℝ × ℝ =>
        (∫ w in {w | q w ≤ p.1},
            H w * ((Real.log p.1 - Real.log (max (q w) p.2) : ℝ) : ℂ) ∂ν)
          - ((Real.log p.1 : ℂ) * ∫ w, H w ∂ν - ∫ w, H w * (Real.log (q w) : ℂ) ∂ν))
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  -- the real error weight
  let c : ℝ × ℝ → Ω → ℝ := fun p w =>
    if q w ≤ p.1 then Real.log (q w) - Real.log (max (q w) p.2)
    else Real.log (q w) - Real.log p.1
  have hc_meas : ∀ p, Measurable (c p) := by
    intro p
    refine Measurable.ite (measurableSet_le hq measurable_const) ?_ ?_
    · exact (Real.measurable_log.comp hq).sub
        (Real.measurable_log.comp (hq.max measurable_const))
    · exact (Real.measurable_log.comp hq).sub measurable_const
  have hF_meas : ∀ p, AEStronglyMeasurable (fun w => H w * ((c p w : ℝ) : ℂ)) ν := by
    intro p
    exact hH.aestronglyMeasurable.mul
      (Complex.measurable_ofReal.comp (hc_meas p)).aestronglyMeasurable
  have hc_bound : ∀ p : ℝ × ℝ, 1 ≤ p.1 → 0 < p.2 → p.2 ≤ 1 → ∀ w, 0 < q w →
      |c p w| ≤ |Real.log (q w)| := by
    intro p hM hr0 hr1 w hw
    simp only [c]
    split_ifs with h
    · rcases le_total p.2 (q w) with h2 | h2
      · rw [max_eq_left h2]; simp
      · rw [max_eq_right h2]
        have h3 : Real.log (q w) ≤ Real.log p.2 := Real.log_le_log hw h2
        have h4 : Real.log p.2 ≤ 0 := Real.log_nonpos hr0.le hr1
        rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
        linarith
    · rw [not_le] at h
      have h3 : Real.log p.1 ≤ Real.log (q w) := Real.log_le_log (by linarith) h.le
      have h4 : 0 ≤ Real.log p.1 := Real.log_nonneg hM
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
  have hc_zero : ∀ p : ℝ × ℝ, ∀ w, q w ≤ p.1 → p.2 ≤ q w → c p w = 0 := by
    intro p w h1 h2
    simp only [c, if_pos h1, max_eq_left h2, sub_self]
  have hnorm : ∀ p : ℝ × ℝ, 1 ≤ p.1 → 0 < p.2 → p.2 ≤ 1 → ∀ w, 0 < q w →
      ‖H w * ((c p w : ℝ) : ℂ)‖ ≤ ‖H w * (Real.log (q w) : ℂ)‖ := by
    intro p hM hr0 hr1 w hw
    rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hc_bound p hM hr0 hr1 w hw) (norm_nonneg _)
  have h_ev : ∀ᶠ p : ℝ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), 1 ≤ p.1 ∧ 0 < p.2 ∧ p.2 ≤ 1 := by
    have h1 : ∀ᶠ M : ℝ in atTop, 1 ≤ M := eventually_ge_atTop 1
    have h2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), 0 < r ∧ r ≤ 1 :=
      Ioc_mem_nhdsGT (by norm_num)
    exact h1.prod_mk h2
  -- dominated convergence for the error integral
  have h_bound : ∀ᶠ p : ℝ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ),
      ∀ᵐ w ∂ν, ‖H w * ((c p w : ℝ) : ℂ)‖ ≤ ‖H w * (Real.log (q w) : ℂ)‖ := by
    filter_upwards [h_ev] with p hp
    filter_upwards [hqpos] with w hw
    exact hnorm p hp.1 hp.2.1 hp.2.2 w hw
  have h_ptwise : ∀ᵐ w ∂ν, Tendsto (fun p : ℝ × ℝ => H w * ((c p w : ℝ) : ℂ))
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    filter_upwards [hqpos] with w hw
    have hev : ∀ᶠ p : ℝ × ℝ in atTop ×ˢ 𝓝[>] (0 : ℝ), q w ≤ p.1 ∧ p.2 ≤ q w := by
      have h1 : ∀ᶠ M : ℝ in atTop, q w ≤ M := eventually_ge_atTop _
      have h2 : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ), r ≤ q w :=
        ((eventually_lt_nhds hw).mono fun _ h => h.le).filter_mono nhdsWithin_le_nhds
      exact h1.prod_mk h2
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with p hp
    simp [hc_zero p w hp.1 hp.2]
  have h_lim : Tendsto (fun p : ℝ × ℝ => ∫ w, H w * ((c p w : ℝ) : ℂ) ∂ν)
      (atTop ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have key := tendsto_integral_filter_of_dominated_convergence
      (μ := ν) (l := atTop ×ˢ 𝓝[>] (0 : ℝ))
      (F := fun p w => H w * ((c p w : ℝ) : ℂ)) (f := fun _ => (0 : ℂ))
      (fun w => ‖H w * (Real.log (q w) : ℂ)‖)
      (Eventually.of_forall hF_meas) h_bound hHlog.norm h_ptwise
    simpa using key
  -- identify the error integral with the stated expression
  refine h_lim.congr' ?_
  filter_upwards [h_ev] with p hp
  have hFint : Integrable (fun w => H w * ((c p w : ℝ) : ℂ)) ν := by
    refine hHlog.norm.mono' (hF_meas p) ?_
    filter_upwards [hqpos] with w hw
    exact hnorm p hp.1 hp.2.1 hp.2.2 w hw
  have hset : MeasurableSet {w | q w ≤ p.1} := measurableSet_le hq measurable_const
  have hpt : ∀ w, Set.indicator {w | q w ≤ p.1}
      (fun w => H w * ((Real.log p.1 - Real.log (max (q w) p.2) : ℝ) : ℂ)) w
      = H w * ((c p w : ℝ) : ℂ) + (Real.log p.1 : ℂ) * H w
        - H w * (Real.log (q w) : ℂ) := by
    intro w
    by_cases h : q w ≤ p.1
    · rw [Set.indicator_of_mem (show w ∈ {w | q w ≤ p.1} from h)]
      simp only [c, if_pos h]
      push_cast
      ring
    · rw [Set.indicator_of_notMem (show w ∉ {w | q w ≤ p.1} from h)]
      simp only [c, if_neg h]
      push_cast
      ring
  have e1 : ∫ w, (H w * ((c p w : ℝ) : ℂ) + (Real.log p.1 : ℂ) * H w
        - H w * (Real.log (q w) : ℂ)) ∂ν
      = ∫ w, (H w * ((c p w : ℝ) : ℂ) + (Real.log p.1 : ℂ) * H w) ∂ν
        - ∫ w, H w * (Real.log (q w) : ℂ) ∂ν :=
    integral_sub (hFint.add (hH.const_mul _)) hHlog
  have e2 : ∫ w, (H w * ((c p w : ℝ) : ℂ) + (Real.log p.1 : ℂ) * H w) ∂ν
      = ∫ w, H w * ((c p w : ℝ) : ℂ) ∂ν + ∫ w, (Real.log p.1 : ℂ) * H w ∂ν :=
    integral_add hFint (hH.const_mul _)
  have e3 : ∫ w, (Real.log p.1 : ℂ) * H w ∂ν = (Real.log p.1 : ℂ) * ∫ w, H w ∂ν :=
    integral_const_mul _ _
  rw [← integral_indicator hset, integral_congr_ae (Eventually.of_forall hpt), e1, e2, e3]
  ring
