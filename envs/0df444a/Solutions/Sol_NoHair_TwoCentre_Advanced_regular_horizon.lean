-- Prove2me | solution 1 for NoHair.TwoCentre.Advanced.regular_horizon
-- status  : ACCEPTED   (prove)
-- author  : @Igor Valuev
-- created : 2026-11-22T21:30:02.772386+00:00
-- url     : https://prove2.me/submissions/643256eb-ff63-4293-a9ed-7d3de1fea2a4

import Definitions.Def_NoHair_TwoCentreAdvanced

open Set Filter Topology
open scoped ContDiff

namespace NoHair.TwoCentre.Advanced

noncomputable section

private theorem collar_positive {p : ℝ × ℝ} (hr : |p.1| < 1 / 4)
    (hc : |p.2| ≤ 1) :
    0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2 ∧ 1 < distanceToOther p ∧ 0 < H p := by
  have hprod : |p.1 * p.2| < 1 / 4 := by
    rw [abs_mul]
    nlinarith [mul_le_mul_of_nonneg_left hc (abs_nonneg p.1)]
  have hsq : (1 : ℝ) ^ 2 < 4 + p.1 ^ 2 - 4 * p.1 * p.2 := by
    nlinarith [(abs_lt.mp hprod).2, sq_nonneg p.1]
  have hd : 1 < distanceToOther p := (Real.lt_sqrt (by norm_num)).2 hsq
  have hi : 0 < 1 / distanceToOther p := one_div_pos.mpr (by linarith)
  have hi' : 1 / distanceToOther p < 1 := (div_lt_one (by linarith)).2 hd
  refine ⟨by linarith, hd, ?_⟩
  unfold H
  nlinarith [mul_nonneg (show 0 ≤ p.1 + 1 / 4 by linarith [(abs_lt.mp hr).1])
    (show 0 ≤ 1 + 1 / distanceToOther p by linarith)]

private theorem gap_factor {p : ℝ × ℝ} (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) :
    H p - H₀ p = p.1 ^ 2 * gapCoeff p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd2 : distanceToOther p ^ 2 = 4 + p.1 ^ 2 - 4 * p.1 * p.2 :=
    Real.sq_sqrt harg.le
  unfold H H₀ gapCoeff
  field_simp [hd.ne', show 2 + distanceToOther p ≠ 0 by linarith]
  linear_combination -p.1 * hd2

private theorem coefficient_analytic {p : ℝ × ℝ}
    (harg : 0 < 4 + p.1 ^ 2 - 4 * p.1 * p.2) (hH : 0 < H p) :
    ∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p := by
  have hd : 0 < distanceToOther p := Real.sqrt_pos.2 harg
  have hd' : 0 < 2 + distanceToOther p := by linarith
  have ds : ContDiffAt ℝ ω distanceToOther p := by
    unfold distanceToOther
    exact (show ContDiffAt ℝ ω (fun q : ℝ × ℝ => 4 + q.1 ^ 2 - 4 * q.1 * q.2) p
      by fun_prop).sqrt harg.ne'
  have hs : ContDiffAt ℝ ω H p := by unfold H; fun_prop (disch := positivity)
  have h0s : ContDiffAt ℝ ω H₀ p := by unfold H₀; fun_prop
  have cs : ContDiffAt ℝ ω gapCoeff p := by unfold gapCoeff; fun_prop (disch := positivity)
  intro f hf
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | rfl <;> apply ContDiffAt.analyticAt <;>
    first | unfold gvv | unfold gvr | unfold grr | unfold angularScale | unfold potentialV |
      unfold potentialR
  all_goals fun_prop (disch := positivity)

private theorem determinant {p : ℝ × ℝ} (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    gvv p * grr p - gvr p ^ 2 = -1 := by
  unfold gvv grr gvr
  field_simp [hH]
  linear_combination (H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap

private theorem match_exterior {p : ℝ × ℝ} (hr : p.1 ≠ 0) (hH : H p ≠ 0)
    (hgap : H p - H₀ p = p.1 ^ 2 * gapCoeff p) :
    grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
      potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1 := by
  constructor
  · unfold grr
    field_simp [hr, hH]
    linear_combination -(H p + H₀ p) * (H p ^ 2 + H₀ p ^ 2) * hgap
  · unfold potentialR
    field_simp [hr, hH]
    linear_combination -H₀ p * hgap

private theorem horizon_values (c : ℝ) :
    gvv (0, c) = 0 ∧ gvr (0, c) = 1 ∧ grr (0, c) = c ∧ angularScale (0, c) = 1 := by
  norm_num [gvv, gvr, grr, angularScale, H, H₀, gapCoeff, distanceToOther]
  ring

private theorem future_radial_negative {b v w a : ℝ} (ha : 0 ≤ a)
    (htime : 2 * v * w + b * w ^ 2 + a < 0)
    (hfuture : -v + (1 - b) * w / 2 < 0) : w < 0 := by
  by_contra! hn
  nlinarith [mul_nonpos_of_nonpos_of_nonneg hfuture.le hn, sq_nonneg w]

/-- A continuous radial coordinate cannot go from nonpositive to positive if all
its zeroes on the interval have strictly inward velocity. -/
private theorem no_outward_crossing {r : ℝ → ℝ} (hc : Continuous r)
    (hzero : ∀ t ∈ Icc (0 : ℝ) 1, r t = 0 → ∃ w < 0, HasDerivAt r w t)
    (hin : r 0 ≤ 0) : r 1 ≤ 0 := by
  by_contra! hout
  let Z := Icc (0 : ℝ) 1 ∩ r ⁻¹' {0}
  have hcompact : IsCompact Z := isCompact_Icc.inter_right (isClosed_singleton.preimage hc)
  obtain ⟨z₀, hz₀, hz₀r⟩ := intermediate_value_Icc zero_le_one hc.continuousOn
    (show 0 ∈ Icc (r 0) (r 1) from ⟨hin, hout.le⟩)
  obtain ⟨z, hz, hmax⟩ := hcompact.exists_isGreatest ⟨z₀, hz₀, hz₀r⟩
  obtain ⟨hzI, hz0⟩ := hz
  change r z = 0 at hz0
  have hzlt : z < 1 := lt_of_le_of_ne hzI.2 (by rintro rfl; linarith)
  obtain ⟨w, hw, hder⟩ := hzero z hzI hz0
  have hright := (hasDerivAt_iff_tendsto_slope_left_right.mp hder).2
  have hneg := hright.eventually_lt_const hw
  have hlt : ∀ᶠ t in 𝓝[>] z, t < 1 :=
    (eventually_lt_nhds hzlt).filter_mono nhdsWithin_le_nhds
  have himp : ∀ᶠ t in 𝓝[>] z, False := by
    filter_upwards [hneg, self_mem_nhdsWithin, hlt] with t hs hzt ht1
    change z < t at hzt
    rw [slope_def_field, hz0, sub_zero] at hs
    have htneg : r t < 0 := (div_neg_iff.mp hs).resolve_left (by
      rintro ⟨_, h⟩; linarith)
      |>.1
    obtain ⟨s, hsI, hsz⟩ := intermediate_value_Icc ht1.le hc.continuousOn
      (show 0 ∈ Icc (r t) (r 1) from ⟨htneg.le, hout.le⟩)
    have hsz' : s ∈ Z := ⟨⟨le_trans hzI.1 (le_trans hzt.le hsI.1), hsI.2⟩, hsz⟩
    linarith [hmax hsz', hsI.1]
  exact himp.exists.elim (fun _ h => h)

end
end NoHair.TwoCentre.Advanced

open NoHair.TwoCentre.Advanced

/-- Across the selected future horizon the advanced metric and gauge potential
have analytic coefficients. The radial block has determinant −1, matches the
advanced expression on the exterior, and timelike curves can only cross inward. -/
theorem solution :
    (∀ p : ℝ × ℝ, |p.1| < 1 / 4 → |p.2| ≤ 1 →
      0 < H p ∧
      (∀ f ∈ [gvv, gvr, grr, angularScale, potentialV, potentialR], AnalyticAt ℝ f p) ∧
      gvv p * grr p - gvr p ^ 2 = -1 ∧
      (0 < p.1 → grr p = (H p ^ 4 - H₀ p ^ 4) / (p.1 ^ 2 * H p ^ 2) ∧
        potentialR p = -(H₀ p ^ 2 / (p.1 * H p)) + H₀ p / p.1)) ∧
    (∀ c : ℝ, gvv (0, c) = 0 ∧ gvr (0, c) = 1 ∧ grr (0, c) = c ∧ angularScale (0, c) = 1) ∧
    (∀ r : ℝ → ℝ, Continuous r → r 0 ≤ 0 →
      (∀ t ∈ Icc (0 : ℝ) 1, r t = 0 → ∃ b v w a : ℝ, HasDerivAt r w t ∧ 0 ≤ a ∧
        2 * v * w + b * w ^ 2 + a < 0 ∧ -v + (1 - b) * w / 2 < 0) → r 1 ≤ 0) := by
  refine ⟨?_, horizon_values, ?_⟩
  · intro p hr hc
    obtain ⟨harg, _, hH⟩ := collar_positive hr hc
    have hgap := gap_factor harg
    exact ⟨hH, coefficient_analytic harg hH, determinant hH.ne' hgap,
      fun h => match_exterior h.ne' hH.ne' hgap⟩
  · intro r hc hin hcurve
    apply no_outward_crossing hc _ hin
    intro t ht hz
    obtain ⟨b, v, w, a, hd, ha, htime, hfuture⟩ := hcurve t ht hz
    exact ⟨w, future_radial_negative ha htime hfuture, hd⟩
