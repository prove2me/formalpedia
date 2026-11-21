-- Prove2me | solution 2 for MasulloRH.regularized_mellin_limit
-- status  : ACCEPTED   (prove)
-- author  : @ijawdoij123
-- created : 2026-11-20T22:10:22.127144+00:00
-- url     : https://prove2.me/submissions/b7c8800a-e28a-4879-bdf8-2cf5ca82cfa8

import Definitions.Def_MasulloRH_RegularizedTrace
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.MellinTransform
import Mathlib.MeasureTheory.Integral.DominatedConvergence

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology ContDiff

private lemma cutoff_mem (n : ℕ) (t : ℝ) :
    0 ≤ MasulloRH.traceLogCutoff n t ∧ MasulloRH.traceLogCutoff n t ≤ 1 := by
  unfold MasulloRH.traceLogCutoff
  split_ifs
  · have a0 := Real.smoothTransition.nonneg (((n : ℝ) + 1) * Real.log t - 1)
    have a1 := Real.smoothTransition.le_one (((n : ℝ) + 1) * Real.log t - 1)
    have b0 := Real.smoothTransition.nonneg (Real.log t / ((n : ℝ) + 1) - 1)
    have b1 := Real.smoothTransition.le_one (Real.log t / ((n : ℝ) + 1) - 1)
    constructor
    · exact mul_nonneg a0 (by linarith)
    · nlinarith
  · exact ⟨le_rfl, zero_le_one⟩

private lemma cutoff_measurable (n : ℕ) : Measurable (MasulloRH.traceLogCutoff n) := by
  unfold MasulloRH.traceLogCutoff
  refine Measurable.ite measurableSet_Ioi ?_ measurable_const
  have h := Real.smoothTransition.continuous
  fun_prop

private lemma cutoff_eventually_one {t : ℝ} (ht : 1 < t) :
    ∀ᶠ n : ℕ in atTop, MasulloRH.traceLogCutoff n t = 1 := by
  have hl : 0 < Real.log t := Real.log_pos ht
  obtain ⟨N₁, hN₁⟩ := exists_nat_gt (2 / Real.log t)
  obtain ⟨N₂, hN₂⟩ := exists_nat_gt (Real.log t)
  filter_upwards [eventually_ge_atTop (max N₁ N₂)] with n hn
  have hn1 : (N₁ : ℝ) ≤ n := by exact_mod_cast (le_max_left _ _).trans hn
  have hn2 : (N₂ : ℝ) ≤ n := by exact_mod_cast (le_max_right _ _).trans hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold MasulloRH.traceLogCutoff
  rw [if_pos ht]
  have e1 : 1 ≤ ((n : ℝ) + 1) * Real.log t - 1 := by
    have : 2 / Real.log t < (n : ℝ) + 1 := by linarith
    rw [div_lt_iff₀ hl] at this
    linarith
  have e2 : Real.log t / ((n : ℝ) + 1) - 1 ≤ 0 := by
    have : Real.log t / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one hpos]; linarith
    linarith
  rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.zero_of_nonpos e2]
  norm_num

/-- The limiting integrand. -/
private noncomputable def gF (s w : ℂ) (t : ℝ) : ℂ :=
  (t : ℂ) ^ (w - s - 1 / 2) - (t : ℂ) ^ (w - 3)

private lemma integrand_eq (n : ℕ) (s w : ℂ) {t : ℝ} (ht : 1 < t) :
    (t : ℂ) ^ (w - 1) • MasulloRH.regularizedTraceTest n s t =
      (MasulloRH.traceLogCutoff n t : ℂ) * gF s w t := by
  have ht0 : (t : ℂ) ≠ 0 := by exact_mod_cast (show (0:ℝ) < t by linarith).ne'
  simp only [MasulloRH.regularizedTraceTest, if_pos ht, smul_eq_mul, gF]
  have h1 : (t : ℂ) ^ (w - s - 1 / 2) = (t : ℂ) ^ (w - 1) * (t : ℂ) ^ (1 / 2 - s) := by
    rw [← Complex.cpow_add _ _ ht0]; ring_nf
  have h2 : (t : ℂ) ^ (w - 3) = (t : ℂ) ^ (w - 1) * (t : ℂ) ^ (-2 : ℂ) := by
    rw [← Complex.cpow_add _ _ ht0]; ring_nf
  rw [h1, h2]; ring

theorem solution (s w : ℂ)
    (hsw : w.re < s.re - 1 / 2) (hw : w.re < 2) :
    Tendsto (fun n : ℕ => mellin (MasulloRH.regularizedTraceTest n s) w) atTop
      (𝓝 (1 / (s - 1 / 2 - w) - 1 / ((2 : ℂ) - w))) := by
  have ha : (w - s - 1 / 2).re < -1 := by simp; linarith
  have hb : (w - 3).re < -1 := by simp; linarith
  have hiA := integrableOn_Ioi_cpow_of_lt ha one_pos
  have hiB := integrableOn_Ioi_cpow_of_lt hb one_pos
  have hint : IntegrableOn (gF s w) (Ioi 1) := hiA.sub hiB
  have hcongr : ∀ n : ℕ, mellin (MasulloRH.regularizedTraceTest n s) w =
      ∫ t in Ioi (1 : ℝ), (MasulloRH.traceLogCutoff n t : ℂ) * gF s w t := by
    intro n
    rw [mellin, setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (Ioi_subset_Ioi zero_le_one)]
    · exact setIntegral_congr_fun measurableSet_Ioi (fun t ht => integrand_eq n s w ht)
    · intro t ht
      have : ¬ (1 < t) := ht.2
      simp [MasulloRH.regularizedTraceTest, this]
  have hlim : (1 / (s - 1 / 2 - w) - 1 / ((2 : ℂ) - w)) = ∫ t in Ioi (1 : ℝ), gF s w t := by
    simp only [gF]
    rw [integral_sub hiA hiB, integral_Ioi_cpow_of_lt ha one_pos,
      integral_Ioi_cpow_of_lt hb one_pos]
    have hA : w - s - 1 / 2 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hB : w - 3 + 1 ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this; linarith
    have hA' : s - 1 / 2 - w ≠ 0 := by
      intro h; apply hA; linear_combination -h
    have hB' : (2 : ℂ) - w ≠ 0 := by
      intro h; apply hB; linear_combination -h
    simp only [Complex.ofReal_one, Complex.one_cpow]
    have e1 : w - s - 1 / 2 + 1 = -(s - 1 / 2 - w) := by ring
    have e2 : w - 3 + 1 = -((2 : ℂ) - w) := by ring
    rw [e1, e2, neg_div_neg_eq, neg_div_neg_eq]
  simp_rw [hcongr]
  rw [hlim]
  refine tendsto_integral_of_dominated_convergence (fun t => ‖gF s w t‖) ?_ hint.norm ?_ ?_
  · intro n
    refine ((Complex.measurable_ofReal.comp (cutoff_measurable n)).aestronglyMeasurable.mul
      hint.aestronglyMeasurable)
  · intro n
    refine ae_of_all _ fun t => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (cutoff_mem n t).1]
    exact mul_le_of_le_one_left (norm_nonneg _) (cutoff_mem n t).2
  · refine (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht => ?_)
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [cutoff_eventually_one ht] with n hn
    rw [hn]; simp
