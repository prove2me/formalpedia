-- Prove2me | solution 1 for MinBuying.budget_characterization
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:16:57.003833+00:00
-- url     : https://prove2.me/submissions/00cf8456-b540-4907-9bd5-33d41e4f853e

import Definitions.Def_MinBuying_Analytic

open Set Filter MinBuying
open scoped Topology

private noncomputable def logSecant : ℝ → ℝ :=
  Function.update (fun y : ℝ => (Real.log y - Real.log 1) / (y - 1)) 1 1

private lemma logSecant_continuous : ContinuousAt logSecant 1 := by
  simpa [logSecant] using (Real.hasDerivAt_log (by norm_num : (1 : ℝ) ≠ 0)).continuousAt_div

private lemma logSecant_formula (x : ℝ) (hx : x ≠ 0) :
    logSecant (1 - x ^ 2) = -Real.log (1 - x ^ 2) / x ^ 2 := by
  have hn : 1 - x ^ 2 ≠ 1 := by nlinarith [sq_pos_of_ne_zero hx]
  simp only [logSecant, Function.update_of_ne hn, Real.log_one, sub_zero]
  field_simp
  ring

private lemma budget_as_secant (x : ℝ) :
    canonicalBudget x = x * logSecant (1 - x ^ 2) := by
  by_cases hx : x = 0
  · simp [hx, canonicalBudget]
  · rw [canonicalBudget, if_neg hx, logSecant_formula x hx]
    field_simp

private lemma slope_as_secant (x : ℝ) :
    budgetSlope x = 2 / (1 - x ^ 2) - logSecant (1 - x ^ 2) := by
  by_cases hx : x = 0
  · norm_num [hx, budgetSlope, logSecant]
  · rw [budgetSlope, if_neg hx, logSecant_formula x hx]
    ring

private lemma secant_comp_continuous :
    ContinuousAt (fun x : ℝ => logSecant (1 - x ^ 2)) 0 := by
  exact logSecant_continuous.comp_of_eq (by fun_prop) (by norm_num)

private lemma budget_deriv_zero : HasDerivAt canonicalBudget 1 0 := by
  have hlim : Tendsto (fun x : ℝ => logSecant (1 - x ^ 2)) (𝓝 0) (𝓝 1) := by
    simpa [logSecant] using secant_comp_continuous.tendsto
  apply hasDerivAt_iff_tendsto_slope.mpr
  have heq : slope canonicalBudget 0 =ᶠ[𝓝[≠] 0]
      (fun x : ℝ => logSecant (1 - x ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    simp only [slope_def_field]
    have hz : canonicalBudget 0 = 0 := by simp [canonicalBudget]
    rw [hz, sub_zero, sub_zero, budget_as_secant]
    field_simp
  exact (tendsto_congr' heq).2 (hlim.mono_left nhdsWithin_le_nhds)

private lemma positive_denominator (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) : 0 < 1 - x ^ 2 := by
  nlinarith [hx.1, hx.2, mul_nonneg hx.1 (le_of_lt (sub_pos.mpr hx.2))]

private lemma budget_derivative (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    HasDerivAt canonicalBudget (budgetSlope x) x := by
  by_cases hx0 : x = 0
  · subst x
    simpa [budgetSlope] using budget_deriv_zero
  · have hd := (((((hasDerivAt_id x).pow 2).const_sub 1).log
        (positive_denominator x hx).ne').neg).div (hasDerivAt_id x) hx0
    have heq : canonicalBudget =ᶠ[𝓝 x] (fun y => -Real.log (1 - y ^ 2) / y) := by
      filter_upwards [eventually_ne_nhds hx0] with y hy
      simp [canonicalBudget, hy]
    convert! hd.congr_of_eventuallyEq heq using 1
    simp only [budgetSlope, if_neg hx0, id_eq, Pi.pow_apply, Pi.neg_apply]
    field_simp
    ring

private lemma slope_continuous (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    ContinuousAt budgetSlope x := by
  by_cases hx0 : x = 0
  · subst x
    have h : ContinuousAt (fun x : ℝ => 2 / (1 - x ^ 2) -
        logSecant (1 - x ^ 2)) 0 :=
      (continuousAt_const.div (by fun_prop) (by norm_num)).sub secant_comp_continuous
    simpa only [← slope_as_secant] using h
  · have hden := positive_denominator x hx
    have hc : ContinuousAt (fun y : ℝ => 1 - y ^ 2) x := by fun_prop
    have hlog : ContinuousAt (fun y : ℝ => Real.log (1 - y ^ 2)) x :=
      hc.log hden.ne'
    have h : ContinuousAt (fun y : ℝ => 2 / (1 - y ^ 2) + Real.log (1 - y ^ 2) / y ^ 2) x :=
      (continuousAt_const.div hc hden.ne').add (hlog.div (by fun_prop) (pow_ne_zero 2 hx0))
    apply h.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds hx0] with y hy
    simp [budgetSlope, hy]

private lemma slope_estimates (x : ℝ) (hx : x ∈ Ico (0 : ℝ) 1) :
    0 < budgetSlope x ∧ budgetSlope x * (1 - x) ^ 2 ≤ 1 - x := by
  by_cases hx0 : x = 0
  · subst x
    norm_num [budgetSlope]
  · have hxpos : 0 < x := lt_of_le_of_ne hx.1 (Ne.symm hx0)
    have hx2 : 0 < x ^ 2 := sq_pos_of_pos hxpos
    have hu := positive_denominator x hx
    have hloglow := Real.one_sub_inv_le_log_of_pos hu
    have hlogup := Real.log_le_sub_one_of_pos hu
    have hlow : -(1 / (1 - x ^ 2)) ≤ Real.log (1 - x ^ 2) / x ^ 2 := by
      apply (le_div_iff₀ hx2).2
      have heq : -(1 / (1 - x ^ 2)) * x ^ 2 = 1 - (1 - x ^ 2)⁻¹ := by
        field_simp
        ring
      rw [heq]
      exact hloglow
    have hup : Real.log (1 - x ^ 2) / x ^ 2 ≤ -1 := by
      apply (div_le_iff₀ hx2).2
      linarith
    have hsl : 1 / (1 - x ^ 2) ≤ budgetSlope x := by
      simp only [budgetSlope, if_neg hx0]
      have htwo : 2 / (1 - x ^ 2) = 1 / (1 - x ^ 2) + 1 / (1 - x ^ 2) := by ring
      rw [htwo]
      linarith
    have hsu : budgetSlope x ≤ 2 / (1 - x ^ 2) - 1 := by
      simp only [budgetSlope, if_neg hx0]
      linarith
    refine ⟨lt_of_lt_of_le (one_div_pos.mpr hu) hsl, ?_⟩
    calc
      budgetSlope x * (1 - x) ^ 2 ≤ (2 / (1 - x ^ 2) - 1) * (1 - x) ^ 2 :=
        mul_le_mul_of_nonneg_right hsu (sq_nonneg _)
      _ = (1 - x) * (1 + x ^ 2) / (1 + x) := by
        field_simp
        ring
      _ ≤ 1 - x := by
        apply (div_le_iff₀ (by linarith : 0 < 1 + x)).2
        have hxx : x ^ 2 ≤ x := by nlinarith [mul_nonneg hx.1 (sub_nonneg.mpr hx.2.le)]
        nlinarith [mul_nonneg (sub_nonneg.mpr hxx) (sub_nonneg.mpr hx.2.le)]

private lemma budget_large_value (s : ℝ) (hs : 0 ≤ s) :
    ∃ y : ℝ, y ∈ Ioo (0 : ℝ) 1 ∧ s ≤ canonicalBudget y := by
  let e := Real.exp (-(s + 1))
  have he : 0 < e := Real.exp_pos _
  have he1 : e < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  let y := Real.sqrt (1 - e)
  have hy : 0 < y := Real.sqrt_pos.mpr (by linarith)
  have hy2 : y ^ 2 = 1 - e := Real.sq_sqrt (by linarith)
  have hy1 : y < 1 := by nlinarith
  have hden : 1 - y ^ 2 = e := by linarith
  have hlog : Real.log (1 - y ^ 2) = -(s + 1) := by
    rw [hden]
    exact Real.log_exp _
  have hA : canonicalBudget y = (s + 1) / y := by
    rw [canonicalBudget, if_neg hy.ne', hlog]
    ring
  refine ⟨y, ⟨hy, hy1⟩, ?_⟩
  rw [hA]
  apply (le_div_iff₀ hy).2
  nlinarith [mul_nonneg hs (sub_nonneg.mpr hy1.le)]

theorem solution :
    canonicalBudget 0 = 0 ∧
    ContinuousOn budgetSlope (Ico (0 : ℝ) 1) ∧
    (∀ x ∈ Ico (0 : ℝ) 1,
      HasDerivWithinAt canonicalBudget (budgetSlope x) (Ico (0 : ℝ) 1) x ∧
      0 < budgetSlope x ∧ budgetSlope x * (1 - x) ^ 2 ≤ 1 - x) ∧
    StrictMonoOn canonicalBudget (Ico (0 : ℝ) 1) ∧
    (∀ s : ℝ, 0 ≤ s → ∃! x : ℝ, x ∈ Ico (0 : ℝ) 1 ∧ canonicalBudget x = s) := by
  have hcont : ContinuousOn canonicalBudget (Ico (0 : ℝ) 1) :=
    fun x hx => (budget_derivative x hx).continuousAt.continuousWithinAt
  have hmono : StrictMonoOn canonicalBudget (Ico (0 : ℝ) 1) := by
    apply strictMonoOn_of_deriv_pos (convex_Ico _ _) hcont
    intro x hx
    rw [(budget_derivative x (interior_subset hx)).deriv]
    exact (slope_estimates x (interior_subset hx)).1
  refine ⟨by simp [canonicalBudget], fun x hx => (slope_continuous x hx).continuousWithinAt,
    fun x hx => ⟨(budget_derivative x hx).hasDerivWithinAt, slope_estimates x hx⟩, hmono, ?_⟩
  intro s hs
  obtain ⟨y, hy, hys⟩ := budget_large_value s hs
  have hc : ContinuousOn canonicalBudget (Icc 0 y) :=
    hcont.mono (fun x hx => ⟨hx.1, lt_of_le_of_lt hx.2 hy.2⟩)
  have hi : s ∈ Icc (canonicalBudget 0) (canonicalBudget y) :=
    ⟨by simpa [canonicalBudget] using hs, hys⟩
  obtain ⟨x, hx, hxs⟩ := intermediate_value_Icc hy.1.le hc hi
  have hxI : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1, lt_of_le_of_lt hx.2 hy.2⟩
  refine ⟨x, ⟨hxI, hxs⟩, ?_⟩
  intro z hz
  exact hmono.injOn hz.1 hxI (hz.2.trans hxs.symm)
