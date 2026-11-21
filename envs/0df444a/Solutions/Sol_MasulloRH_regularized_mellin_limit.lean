-- Prove2me | solution 1 for MasulloRH.regularized_mellin_limit
-- status  : ACCEPTED   (prove)
-- author  : @Yi
-- created : 2026-11-20T22:09:28.670383+00:00
-- url     : https://prove2.me/submissions/b5e3e615-fb80-4897-90e5-369822212e44

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MasulloRH MeasureTheory Set Filter
open scoped Topology

private theorem cutoff_mem_Icc (n : ℕ) {t : ℝ} (ht : 1 < t) : traceLogCutoff n t ∈ Icc 0 1 := by
  rw [traceLogCutoff, if_pos ht]
  exact ⟨mul_nonneg (Real.smoothTransition.nonneg _) (sub_nonneg.mpr (Real.smoothTransition.le_one _)),
    mul_le_one₀ (Real.smoothTransition.le_one _) (sub_nonneg.mpr (Real.smoothTransition.le_one _))
      (sub_le_self _ (Real.smoothTransition.nonneg _))⟩

private theorem cutoff_eventually_one {t : ℝ} (ht : 1 < t) :
    ∀ᶠ n : ℕ in atTop, traceLogCutoff n t = 1 := by
  have hlog := Real.log_pos ht
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hcast.eventually_ge_atTop (2 / Real.log t),
    hcast.eventually_ge_atTop (Real.log t)] with n hn hn'
  have h1 : 1 ≤ ((n : ℝ) + 1) * Real.log t - 1 := by
    nlinarith [(div_le_iff₀ hlog).mp hn]
  have h2 : Real.log t / ((n : ℝ) + 1) - 1 ≤ 0 := by
    apply sub_nonpos.mpr
    apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
    linarith
  simp [traceLogCutoff, ht, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.zero_of_nonpos h2]

private theorem cutoff_integral_tendsto {f : ℝ → ℂ} (hf : IntegrableOn f (Ioi 1)) :
    Tendsto (fun n => ∫ t in Ioi (1 : ℝ), (traceLogCutoff n t : ℂ) * f t)
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), f t)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => ‖f t‖) ?_ hf.norm ?_ ?_
  · intro n
    have hm : Measurable (traceLogCutoff n) := by
      unfold traceLogCutoff
      apply Measurable.ite measurableSet_Ioi
      · fun_prop
      · fun_prop
    exact (Complex.measurable_ofReal.comp hm).aestronglyMeasurable.mul hf.aestronglyMeasurable
  · intro n
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    have hc := cutoff_mem_Icc n ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hc.1]
    exact mul_le_of_le_one_left (norm_nonneg _) hc.2
  · filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioi] with t ht
    apply Filter.EventuallyEq.tendsto
    filter_upwards [cutoff_eventually_one ht] with n hn
    simp [hn]

theorem solution (s w : ℂ) (hsw : w.re < s.re - 1 / 2) (hw : w.re < 2) :
    Tendsto (fun n : ℕ => mellin (regularizedTraceTest n s) w) atTop
      (𝓝 (1 / (s - 1 / 2 - w) - 1 / ((2 : ℂ) - w))) := by
  let a := (w - 1) + (1 / 2 - s)
  let b := (w - 1) + (-2 : ℂ)
  have ha : a.re < -1 := by dsimp [a]; norm_num at *; linarith
  have hb : b.re < -1 := by dsimp [b]; norm_num at *; linarith
  have hia := integrableOn_Ioi_cpow_of_lt ha (c := (1 : ℝ)) zero_lt_one
  have hib := integrableOn_Ioi_cpow_of_lt hb (c := (1 : ℝ)) zero_lt_one
  let f := fun t : ℝ => (t : ℂ) ^ a - (t : ℂ) ^ b
  have hM (n : ℕ) :
      mellin (regularizedTraceTest n s) w = ∫ t in Ioi (1 : ℝ), (traceLogCutoff n t : ℂ) * f t := by
    unfold mellin
    calc
      _ = ∫ t in Ioi (1 : ℝ), (t : ℂ) ^ (w - 1) • regularizedTraceTest n s t := by
        apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
          (Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
        intro t ht
        simp [regularizedTraceTest, show ¬ 1 < t from ht.2]
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro t ht
        have ht' := Complex.ofReal_ne_zero.mpr (zero_lt_one.trans ht).ne'
        simp only [regularizedTraceTest, if_pos (show 1 < t from ht), smul_eq_mul, f,
          a, b, Complex.cpow_add _ _ ht']
        ring
  have hI : (∫ t in Ioi (1 : ℝ), f t) = 1 / (s - 1 / 2 - w) - 1 / ((2 : ℂ) - w) := by
    unfold f
    rw [integral_sub hia hib, integral_Ioi_cpow_of_lt ha zero_lt_one, integral_Ioi_cpow_of_lt hb zero_lt_one]
    simp only [Complex.ofReal_one, Complex.one_cpow]
    rw [show a + 1 = -(s - 1 / 2 - w) by dsimp [a]; ring,
      show b + 1 = -(2 - w) by dsimp [b]; ring]
    simp only [neg_div_neg_eq]
  simpa only [hM, ← hI] using cutoff_integral_tendsto (f := f) (hia.sub hib)
