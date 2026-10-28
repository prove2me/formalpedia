-- Prove2me | solution 1 for OAI.CubicTorus.NestingGain.integrated_uniform_gain
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-28T16:57:01.612001+00:00
-- url     : https://prove2.me/submissions/9e6ade71-9550-45b3-8944-a0f89a3b7fe0

import Mathlib
import Definitions.Def_OAIQ079A000

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_SectionExtentBounds
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

section

noncomputable section
open Set MeasureTheory
open scoped ENNReal

namespace CubicTorus.Nesting

lemma cutoff_pos : 0 < cutoff := by
  unfold cutoff
  positivity

lemma cutoff_sq : cutoff ^ 2 = 48 / 49 := by
  norm_num [cutoff, div_pow]

lemma cutoff_lt_one : cutoff < 1 := by
  nlinarith [cutoff_sq, cutoff_pos]

lemma continuousOn_rawWeight : ContinuousOn rawWeight (Icc 0 cutoff) := by
  have hs : ∀ x ∈ Icc 0 cutoff, Real.sqrt (1 - x ^ 2) ≠ 0 := by
    intro x hx
    apply ne_of_gt (Real.sqrt_pos.2 _)
    have hxl : x < 1 := lt_of_le_of_lt hx.2 cutoff_lt_one
    nlinarith [hx.1, sq_nonneg x]
  exact (continuousOn_const.sub (continuousOn_const.mul (continuousOn_id.pow 2))).div
    ((Real.continuous_sqrt.comp (continuous_const.sub (continuous_id.pow 2))).continuousOn) hs

lemma product_sqrt_le_half {x : ℝ} (hx : x ∈ Icc 0 1) :
    x * Real.sqrt (1 - x ^ 2) ≤ 1 / 2 := by
  have hr : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  nlinarith [Real.sq_sqrt hr, sq_nonneg (x - Real.sqrt (1 - x ^ 2))]

lemma product_sqrt_le_of_lower {a x d : ℝ} (ha : 0 ≤ a) (hax : a ≤ x)
    (hx1 : x ≤ 1) (ha2 : 1 / 2 ≤ a ^ 2) (hd : 0 ≤ d)
    (had : a ^ 2 * (1 - a ^ 2) ≤ d ^ 2) :
    x * Real.sqrt (1 - x ^ 2) ≤ d := by
  have hx0 := le_trans ha hax
  have hxa := pow_le_pow_left₀ ha hax 2
  have hr : 0 ≤ 1 - x ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hr
  have hxs := congrArg (fun t : ℝ => x ^ 2 * t) hs
  have hp : (x ^ 2 - a ^ 2) * (1 - a ^ 2 - x ^ 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith) (by nlinarith)
  apply (sq_le_sq₀ (mul_nonneg hx0 (Real.sqrt_nonneg _)) hd).1
  nlinarith

lemma weight_derivative_bound_of_row {x n d : ℝ} (hx : x ∈ Ico 0 1)
    (hn : n * (1 - x ^ 2) ≤ 48 / 100 - (49 / 100 : ℝ) * x ^ 2)
    (hd : x * Real.sqrt (1 - x ^ 2) ≤ d) (hnd : (91 / 100 : ℝ) * d ≤ n) :
    (91 / 100 : ℝ) * x ≤
      (48 / 100 - (49 / 100 : ℝ) * x ^ 2) / Real.sqrt (1 - x ^ 2) ^ 3 := by
  have hr : 0 < 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hs : 0 < Real.sqrt (1 - x ^ 2) := Real.sqrt_pos.2 hr
  apply (le_div_iff₀ (pow_pos hs 3)).2
  calc
    (91 / 100 : ℝ) * x * Real.sqrt (1 - x ^ 2) ^ 3 =
        ((91 / 100 : ℝ) * (x * Real.sqrt (1 - x ^ 2))) * Real.sqrt (1 - x ^ 2) ^ 2 := by ring
    _ ≤ ((91 / 100 : ℝ) * d) * Real.sqrt (1 - x ^ 2) ^ 2 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hd (by norm_num)) (sq_nonneg _)
    _ ≤ n * Real.sqrt (1 - x ^ 2) ^ 2 := mul_le_mul_of_nonneg_right hnd (sq_nonneg _)
    _ = n * (1 - x ^ 2) := by rw [Real.sq_sqrt (le_of_lt hr)]
    _ ≤ 48 / 100 - (49 / 100 : ℝ) * x ^ 2 := hn

theorem weight_derivative_bound {x : ℝ} (hx : x ∈ Icc 0 (24 / 25 : ℝ)) :
    (91 / 100 : ℝ) * x ≤
      (48 / 100 - (49 / 100 : ℝ) * x ^ 2) / Real.sqrt (1 - x ^ 2) ^ 3 := by
  have hx1 : x ∈ Ico 0 1 := ⟨hx.1, by linarith [hx.2]⟩
  by_cases h84 : x ≤ 84 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h84 2
    apply weight_derivative_bound_of_row (n := 456 / 1000) (d := 1 / 2) hx1
    · nlinarith
    · exact product_sqrt_le_half ⟨hx.1, le_of_lt hx1.2⟩
    · norm_num
  by_cases h89 : x ≤ 89 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h89 2
    apply weight_derivative_bound_of_row (n := 44 / 100) (d := 46 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 84 / 100) (by norm_num) (le_of_not_ge h84)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num
  by_cases h94 : x ≤ 94 / 100
  · have hsq := pow_le_pow_left₀ hx.1 h94 2
    apply weight_derivative_bound_of_row (n := 40 / 100) (d := 41 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 89 / 100) (by norm_num) (le_of_not_ge h89)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num
  · have hsq := pow_le_pow_left₀ hx.1 hx.2 2
    apply weight_derivative_bound_of_row (n := 36 / 100) (d := 33 / 100) hx1
    · nlinarith
    · apply product_sqrt_le_of_lower (a := 94 / 100) (by norm_num) (le_of_not_ge h94)
        (le_of_lt hx1.2) <;> norm_num
    · norm_num

lemma hasDerivAt_squaredWeight {r : ℝ} (hr : r < 1) :
    HasDerivAt squaredWeight
      (-((48 / 100 - (49 / 100 : ℝ) * r) / Real.sqrt (1 - r) ^ 3)) r := by
  have hrad : 0 < 1 - r := sub_pos.2 hr
  have hs := ((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).sqrt (ne_of_gt hrad)
  have hs2 := Real.sq_sqrt (le_of_lt hrad)
  have hs0 := ne_of_gt (Real.sqrt_pos.2 hrad)
  have hh := ((hasDerivAt_const r (1 : ℝ)).sub
    ((hasDerivAt_id r).const_mul lambda)).div hs hs0
  convert hh using 1 <;> try rfl
  dsimp [lambda]
  field_simp
  linear_combination 9800 * hs2

lemma squaredWeight_eq_rawWeight {r : ℝ} (hr : 0 ≤ r) :
    squaredWeight r = rawWeight (Real.sqrt r) := by
  simp only [squaredWeight, rawWeight, Real.sq_sqrt hr]

lemma squaredWeight_difference {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hb : b ≤ (24 / 25 : ℝ) ^ 2) :
    (91 / 100 : ℝ) * Real.sqrt a * (b - a) ≤ squaredWeight a - squaredWeight b := by
  have hi : ∀ r ∈ Icc a b, 0 ≤ r ∧ r < 1 := fun r hr => ⟨le_trans ha hr.1, by linarith [hr.2]⟩
  have hc : ContinuousOn squaredWeight (Icc a b) := by
    intro r hr
    exact (hasDerivAt_squaredWeight (hi r hr).2).continuousAt.continuousWithinAt
  have hm : AntitoneOn (fun r => squaredWeight r + (91 / 100 : ℝ) * Real.sqrt a * r) (Icc a b) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := fun r =>
      -((48 / 100 - (49 / 100 : ℝ) * r) / Real.sqrt (1 - r) ^ 3) +
        (91 / 100 : ℝ) * Real.sqrt a) (convex_Icc a b)
    · exact hc.add (continuousOn_const.mul continuousOn_id)
    · intro r hr
      rw [interior_Icc] at hr
      convert ((hasDerivAt_squaredWeight (hi r ⟨le_of_lt hr.1, le_of_lt hr.2⟩).2).add
        ((hasDerivAt_id r).const_mul ((91 / 100 : ℝ) * Real.sqrt a))).hasDerivWithinAt using 1 <;> try rfl
      simp only [mul_one]
    · intro r hr
      rw [interior_Icc] at hr
      have hr0 := le_trans ha (le_of_lt hr.1)
      have hs : Real.sqrt r ∈ Icc 0 (24 / 25 : ℝ) :=
        ⟨Real.sqrt_nonneg _, Real.sqrt_le_iff.2 ⟨by norm_num, le_trans (le_of_lt hr.2) hb⟩⟩
      have hbound := weight_derivative_bound hs
      rw [Real.sq_sqrt hr0] at hbound
      have hmon := Real.sqrt_le_sqrt (le_of_lt hr.1)
      linarith
  have hh := hm ⟨le_refl a, hab⟩ ⟨hab, le_refl b⟩ hab
  linarith

theorem pointwise_weight_gain {x K : ℝ} (hx : x ∈ Icc 0 (24 / 25 : ℝ)) (hK : 0 ≤ K) :
    (91 / 100 : ℝ) * x ^ 3 * K / Real.sqrt (1 + K) ^ 3 ≤
      weight (x / Real.sqrt (1 + K)) - weight x := by
  have hp : 0 < 1 + K := by linarith
  have hs0 : 0 < Real.sqrt (1 + K) := Real.sqrt_pos.2 hp
  have hs1 : 1 ≤ Real.sqrt (1 + K) := by
    nlinarith [Real.sq_sqrt (le_of_lt hp), Real.sqrt_nonneg (1 + K)]
  have hy0 : 0 ≤ x / Real.sqrt (1 + K) := div_nonneg hx.1 (le_of_lt hs0)
  have hyx : x / Real.sqrt (1 + K) ≤ x := (div_le_iff₀ hs0).2 (by nlinarith [hx.1])
  have hd : (24 / 25 : ℝ) < cutoff := by nlinarith [cutoff_sq, cutoff_pos]
  have hc1 : x ≤ cutoff := le_trans hx.2 (le_of_lt hd)
  have hc2 : x / Real.sqrt (1 + K) ≤ cutoff := le_trans hyx hc1
  rw [weight, min_eq_left hc2, weight, min_eq_left hc1]
  have ha : 0 ≤ x ^ 2 / (1 + K) := div_nonneg (sq_nonneg x) (le_of_lt hp)
  have hab : x ^ 2 / (1 + K) ≤ x ^ 2 := (div_le_iff₀ hp).2 (by nlinarith [sq_nonneg x])
  have hb := pow_le_pow_left₀ hx.1 hx.2 2
  have hg := squaredWeight_difference ha hab hb
  have heqa : Real.sqrt (x ^ 2 / (1 + K)) = x / Real.sqrt (1 + K) := by
    rw [Real.sqrt_div (sq_nonneg x), Real.sqrt_sq hx.1]
  rw [squaredWeight_eq_rawWeight ha, squaredWeight_eq_rawWeight (sq_nonneg x),
    heqa, Real.sqrt_sq hx.1] at hg
  convert hg using 1
  all_goals try with_reducible_and_instances rfl
  have hs2 := Real.sq_sqrt (le_of_lt hp)
  field_simp
  linear_combination -x ^ 3 * K * hs2

end CubicTorus.Nesting

noncomputable section
open Set MeasureTheory
open scoped Interval

namespace CubicTorus.Shape

lemma positive_quadratic_root {a : ℝ} (ha : 0 < a) :
    let r := 2 / (1 + Real.sqrt (1 + 4 * a / Real.pi))
    0 < r ∧ r < 1 ∧ a * r ^ 2 = Real.pi * (1 - r) := by
  have hp := Real.pi_pos
  have hr : 1 < 1 + 4 * a / Real.pi := by
    have : 0 < 4 * a / Real.pi := by positivity
    linarith
  have hs0 := Real.sqrt_nonneg (1 + 4 * a / Real.pi)
  have hs := Real.sq_sqrt (by linarith : 0 ≤ 1 + 4 * a / Real.pi)
  have hs1 : 1 < Real.sqrt (1 + 4 * a / Real.pi) := by nlinarith
  have hd : 0 < 1 + Real.sqrt (1 + 4 * a / Real.pi) := by linarith
  refine ⟨div_pos (by norm_num) hd, (div_lt_one hd).2 (by linarith), ?_⟩
  generalize hz : Real.sqrt (1 + 4 * a / Real.pi) = z at *
  field_simp at hs ⊢
  nlinarith

lemma t_spec {h : ℝ} (hh : 0 < h) :
    0 < t h ∧ t h < 1 ∧ h ^ 2 * t h ^ 2 = Real.pi * (1 - t h) := by
  exact positive_quadratic_root (sq_pos_of_pos hh)

theorem interval_placement {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    (1033 / 2700 : ℝ) ≤ u h - dm ∧ (38 / 100 : ℝ) < u h - dm ∧
    1 / Real.pi < (38 / 100 : ℝ) ∧ u h ≤ 1 - 1 / Real.pi ∧
    u h < t h ∧ h * u h ≤ 24 / 25 := by
  have hp := Real.pi_pos
  have hp3 := Real.pi_gt_three
  have hh0 : 0 < h := by linarith [hh.1]
  have hu1 : u h ≤ 1 - 1 / Real.pi := min_le_left _ _
  have huv : u h ≤ (24 / 25 : ℝ) / h := min_le_right _ _
  have hu : (16 / 27 : ℝ) ≤ u h := by
    apply le_min
    · apply (le_sub_iff_add_le).2
      have hip : 1 / Real.pi ≤ (1 / 3 : ℝ) := (div_le_div_of_nonneg_left (by norm_num) (by norm_num) (le_of_lt hp3))
      linarith
    · apply (le_div_iff₀ hh0).2
      linarith [hh.2]
  have hhU : h * u h ≤ 24 / 25 := by
    have := (le_div_iff₀ hh0).1 huv
    nlinarith
  have htr := t_spec hh0
  have hlt : u h < t h := by
    by_contra! hn
    have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt htr.1) hn 2) (sq_nonneg h)
    have hsq := pow_le_pow_left₀ (mul_nonneg (le_of_lt hh0) (by linarith : 0 ≤ u h)) hhU 2
    have hip : 1 ≤ Real.pi * (1 - u h) := by
      have hh := mul_le_mul_of_nonneg_left hu1 (le_of_lt hp)
      field_simp at hh
      nlinarith
    nlinarith [htr.2.2]
  refine ⟨?_, ?_, ?_, hu1, hlt, hhU⟩
  · dsimp [dm]; linarith
  · dsimp [dm]; linarith
  · apply (div_lt_iff₀ hp).2
    nlinarith

lemma theta_spec : 0 < theta ∧ theta < 1 ∧ c * dm * theta ^ 2 = Real.pi * (1 - theta) := by
  simpa only [theta, mul_assoc] using positive_quadratic_root (a := c * dm) (by norm_num [c, dm])

lemma theta_bounds : (32 / 37 : ℝ) < theta ∧ theta < 13 / 15 := by
  have ht := theta_spec
  have hp := Real.pi_gt_d2
  have hpU : Real.pi < (22 / 7 : ℝ) := by linarith [Real.pi_lt_d4]
  have hr := ht.2.2
  norm_num [c, dm] at hr
  constructor
  · by_contra! hn
    have hs := pow_le_pow_left₀ (le_of_lt ht.1) hn 2
    have hh := mul_lt_mul_of_pos_right hp (by linarith : 0 < 1 - theta)
    nlinarith
  · by_contra! hn
    have hs := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 13 / 15) hn 2
    have hh := mul_lt_mul_of_pos_right hpU (by linarith : 0 < 1 - theta)
    nlinarith

lemma shape_on_left {q : ℝ} (hq : q ∈ Icc 0 theta) : shape q = q ^ 2 := by
  apply min_eq_left
  apply (le_div_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq.1 hq.2 2)
    (by norm_num [c, dm] : 0 ≤ c * dm)
  have ht := theta_spec.2.2
  have hp := mul_le_mul_of_nonneg_left hq.2 (le_of_lt Real.pi_pos)
  nlinarith

lemma shape_on_right {q : ℝ} (hq : q ∈ Icc theta 1) :
    shape q = Real.pi * (1 - q) / (c * dm) := by
  apply min_eq_right
  apply (div_le_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
  have hm := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (le_of_lt theta_spec.1) hq.1 2)
    (by norm_num [c, dm] : 0 ≤ c * dm)
  have ht := theta_spec.2.2
  have hp := mul_le_mul_of_nonneg_left hq.1 (le_of_lt Real.pi_pos)
  nlinarith

lemma shape_nonneg {q : ℝ} (hq : q ∈ Icc 0 1) : 0 ≤ shape q := by
  exact le_min (sq_nonneg q) (div_nonneg
    (mul_nonneg (le_of_lt Real.pi_pos) (sub_nonneg.2 hq.2)) (by norm_num [c, dm]))

lemma shape_max {q : ℝ} (hq : q ∈ Icc 0 1) : shape q ≤ theta ^ 2 := by
  by_cases hh : q ≤ theta
  · rw [shape_on_left ⟨hq.1, hh⟩]
    exact pow_le_pow_left₀ hq.1 hh 2
  · rw [shape_on_right ⟨le_of_not_ge hh, hq.2⟩]
    apply (div_le_iff₀ (by norm_num [c, dm] : 0 < c * dm)).2
    have ht := theta_spec.2.2
    have hp := mul_le_mul_of_nonneg_left (le_of_not_ge hh) (le_of_lt Real.pi_pos)
    nlinarith

lemma continuous_shape : Continuous shape := by
  unfold shape
  fun_prop

lemma integral_eq_split : moment = theta ^ 3 / 3 +
    Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
  have hfi : IntervalIntegrable shape volume 0 theta := continuous_shape.intervalIntegrable 0 theta
  have hfi2 : IntervalIntegrable shape volume theta 1 := continuous_shape.intervalIntegrable theta 1
  have h0 := theta_spec
  unfold moment
  rw [← intervalIntegral.integral_add_adjacent_intervals hfi hfi2]
  have hleft : (∫ q in (0 : ℝ)..theta, shape q) = theta ^ 3 / 3 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 2) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      exact shape_on_left hq
  have hright : (∫ q in theta..(1 : ℝ), shape q) =
      Real.pi / (c * dm) * (1 - theta) ^ 2 / 2 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (1 - q)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume theta 1 from continuous_const.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)]
      norm_num
      ring
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hleft, hright]

lemma moment_eq : moment = theta ^ 2 * (3 - theta) / 6 := by
  rw [integral_eq_split]
  have ht := theta_spec.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 567 : ℝ) * (1 - theta) * ht

lemma firstMoment_eq : firstMoment = theta ^ 2 * (2 + 2 * theta - theta ^ 2) / 12 := by
  have hc : Continuous (fun q : ℝ => q * shape q) := continuous_id.mul continuous_shape
  have h0 := theta_spec
  unfold firstMoment
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable (0 : ℝ) theta) (hc.intervalIntegrable theta (1 : ℝ))]
  have hl : (∫ q in (0 : ℝ)..theta, q * shape q) = theta ^ 4 / 4 := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => q ^ 3) ?_]
    · norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.1)] at hq
      dsimp only
      rw [shape_on_left hq]
      ring
  have hr : (∫ q in theta..(1 : ℝ), q * shape q) =
      Real.pi / (c * dm) * ((1 - theta ^ 2) / 2 - (1 - theta ^ 3) / 3) := by
    rw [intervalIntegral.integral_congr (g := fun q : ℝ => Real.pi / (c * dm) * (q - q ^ 2)) ?_]
    · rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_sub
          (show IntervalIntegrable (fun q : ℝ => q) volume theta 1 from continuous_id.intervalIntegrable _ _)
          (show IntervalIntegrable (fun q : ℝ => q ^ 2) volume theta 1 from (continuous_id.pow 2).intervalIntegrable _ _)]
      norm_num
    · intro q hq
      rw [uIcc_of_le (le_of_lt h0.2.1)] at hq
      dsimp only
      rw [shape_on_right hq]
      ring
  rw [hl, hr]
  have ht := h0.2.2
  norm_num [c, dm] at ht ⊢
  linear_combination -(500 / 1701 : ℝ) * (1 - theta) * (1 + 2 * theta) * ht

lemma moment_pos : 0 < moment := by
  rw [moment_eq]
  have ht := theta_spec
  have h3 : 0 < 3 - theta := by linarith [ht.2.1]
  have htpos := ht.1
  positivity

lemma meanQ_eq : meanQ = (2 + 2 * theta - theta ^ 2) / (2 * (3 - theta)) := by
  unfold meanQ
  rw [moment_eq, firstMoment_eq]
  have ht := theta_spec
  have ht0 := ne_of_gt ht.1
  have h30 : 3 - theta ≠ 0 := by linarith [ht.2.1]
  field_simp [ht0, h30]
  ring

lemma meanQ_mem : meanQ ∈ Ioo 0 1 := by
  rw [meanQ_eq]
  have ht := theta_spec
  have hs : theta ^ 2 < 1 := by nlinarith [ht.1, ht.2.1]
  constructor
  · apply div_pos
    · nlinarith
    · linarith
  · apply (div_lt_one (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 2)]

theorem moment_bounds : (2659 / 10000 : ℝ) < moment ∧
    (697 / 1000 : ℝ) < meanQ ∧ p₂ < (109 / 100 : ℝ) := by
  have ht := theta_spec
  have hb := theta_bounds
  have hθ2 := pow_lt_pow_left₀ hb.1 (by norm_num : (0 : ℝ) ≤ 32 / 37) (by norm_num : (2 : ℕ) ≠ 0)
  have hθU := pow_lt_pow_left₀ hb.2 (le_of_lt ht.1) (by norm_num : (2 : ℕ) ≠ 0)
  refine ⟨?_, ?_, ?_⟩
  · rw [moment_eq]
    have hm : 0 ≤ (theta ^ 2 - (32 / 37) ^ 2) * (3 - theta) :=
      mul_nonneg (by linarith) (by linarith [ht.2.1])
    nlinarith [hb.2]
  · rw [meanQ_eq]
    apply (lt_div_iff₀ (by linarith : 0 < 2 * (3 - theta))).2
    nlinarith [sq_nonneg (theta - 1)]
  · dsimp [p₂, c, dm]
    nlinarith

lemma affine_shape_integral (a b : ℝ) :
    (∫ q in (0 : ℝ)..1, (a + b * q) * shape q) = moment * (a + b * meanQ) := by
  have hc : IntervalIntegrable shape volume 0 1 := continuous_shape.intervalIntegrable 0 1
  have hq : IntervalIntegrable (fun q : ℝ => q * shape q) volume 0 1 :=
    (continuous_id.mul continuous_shape).intervalIntegrable 0 1
  have heq : (fun q : ℝ => (a + b * q) * shape q) =
      fun q => a * shape q + b * (q * shape q) := by funext q; ring
  rw [heq, intervalIntegral.integral_add (hc.const_mul a) (hq.const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  change a * moment + b * firstMoment = moment * (a + b * meanQ)
  unfold meanQ
  field_simp [ne_of_gt moment_pos]

lemma cubic_shape_lower {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    moment * (a + b * meanQ) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (a + b * q) ^ 3 * shape q := by
  let m := a + b * meanQ
  have hm : 0 ≤ m := add_nonneg ha (mul_nonneg hb (le_of_lt meanQ_mem.1))
  have hc : IntervalIntegrable (fun q : ℝ => (a + b * q) ^ 3 * shape q) volume 0 1 :=
    (((continuous_const.add (continuous_const.mul continuous_id)).pow 3).mul continuous_shape).intervalIntegrable 0 1
  have h1 : IntervalIntegrable (fun q : ℝ => m ^ 3 * shape q) volume 0 1 :=
    (continuous_const.mul continuous_shape).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun q : ℝ => (a + b * q - m) * shape q) volume 0 1 :=
    (( (continuous_const.add (continuous_const.mul continuous_id)).sub continuous_const).mul continuous_shape).intervalIntegrable 0 1
  have hbound := intervalIntegral.integral_mono_on (show (0 : ℝ) ≤ 1 by norm_num)
    (h1.add (h2.const_mul (3 * m ^ 2))) hc (fun q hq => by
      have hs := shape_nonneg hq
      have hf : 0 ≤ a + b * q := add_nonneg ha (mul_nonneg hb hq.1)
      have hh := mul_nonneg (mul_nonneg (sq_nonneg (a + b * q - m))
        (show 0 ≤ a + b * q + 2 * m by linarith)) hs
      nlinarith)
  rw [intervalIntegral.integral_add h1 (h2.const_mul (3 * m ^ 2)),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hbound
  have hz : (∫ q in (0 : ℝ)..1, (a + b * q - m) * shape q) = 0 := by
    have heq : (fun q : ℝ => (a + b * q - m) * shape q) =
        fun q => (a - m + b * q) * shape q := by funext q; ring
    rw [heq, affine_shape_integral]
    dsimp [m]
    ring
  rw [hz, mul_zero, add_zero] at hbound
  change moment * m ^ 3 ≤ _
  change m ^ 3 * moment ≤ _ at hbound
  linarith only [hbound]

lemma cubic_shape_lower_dm {u₀ δ : ℝ} (hδ : δ ∈ Icc 0 dm) (hu : dm ≤ u₀) :
    moment * (u₀ - (1 - meanQ) * dm) ^ 3 ≤
      ∫ q in (0 : ℝ)..1, (u₀ - δ + δ * q) ^ 3 * shape q := by
  have hm := meanQ_mem
  have h1 := cubic_shape_lower (a := u₀ - δ) (b := δ) (by linarith [hδ.2]) hδ.1
  apply le_trans _ h1
  apply mul_le_mul_of_nonneg_left _ (le_of_lt moment_pos)
  have hb : u₀ - (1 - meanQ) * dm ≤ u₀ - δ + δ * meanQ := by
    have hh := mul_le_mul_of_nonneg_left hδ.2 (show 0 ≤ 1 - meanQ by linarith [hm.2])
    nlinarith
  apply pow_le_pow_left₀ _ hb 3
  have hh : 0 ≤ dm * meanQ := mul_nonneg (by norm_num [dm]) (le_of_lt hm.1)
  nlinarith

lemma p₂_pos : 0 < p₂ := by
  unfold p₂ c dm
  positivity

lemma coefficient_lower : (574 / 1000 : ℝ) <
    ((91 / 100 : ℝ) * c * moment) / Real.sqrt p₂ ^ 3 := by
  have hM := moment_bounds.1
  have hp := moment_bounds.2.2
  have hs : 0 < Real.sqrt p₂ := Real.sqrt_pos.2 p₂_pos
  have hs2 := Real.sq_sqrt (le_of_lt p₂_pos)
  have hd : (Real.sqrt p₂ ^ 3) ^ 2 = p₂ ^ 3 := by
    rw [show (Real.sqrt p₂ ^ 3) ^ 2 = (Real.sqrt p₂ ^ 2) ^ 3 by ring, hs2]
  have hp3 := pow_lt_pow_left₀ hp (le_of_lt p₂_pos) (by norm_num : (3 : ℕ) ≠ 0)
  have hc : (574 / 1000 : ℝ) * Real.sqrt p₂ ^ 3 <
      (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ) := by
    apply (sq_lt_sq₀ (by positivity)
      (by norm_num [c] : (0 : ℝ) ≤ (91 / 100 : ℝ) * c * (2659 / 10000 : ℝ))).1
    rw [mul_pow, hd]
    norm_num [c]
    nlinarith only [hp3]
  apply (lt_div_iff₀ (pow_pos hs 3)).2
  have hmc := mul_lt_mul_of_pos_left hM (by norm_num [c] : (0 : ℝ) < (91 / 100 : ℝ) * c)
  exact lt_trans hc hmc

end CubicTorus.Shape
end
end
end
end

end OAI
end

section
-- module Solutions.OAIQ079_CT.CubicTorus_Profiles_NestingEndpointBound
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
section
noncomputable section
open Set MeasureTheory
open scoped ENNReal
noncomputable section
open Set MeasureTheory
open scoped Interval
namespace CubicTorus.Shape

theorem uniform_coefficient {h : ℝ} (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) ≤
      ((91 / 100 : ℝ) * c * moment / Real.sqrt p₂ ^ 3) *
        (h * (u h - (1 - meanQ) * dm)) ^ 3 := by
  let d₀ : ℝ := (1 - meanQ) * dm
  have hd0 : 0 ≤ d₀ := mul_nonneg (by linarith [meanQ_mem.2]) (by norm_num [dm])
  have hd : d₀ ≤ (6363 / 100000 : ℝ) := by
    dsimp [d₀, dm]
    linarith [moment_bounds.2.1]
  have hh0 : 0 < h := by linarith [hh.1]
  have hc := coefficient_lower
  by_cases hbranch : 1 - 1 / Real.pi ≤ (24 / 25 : ℝ) / h
  · have hip : 1 / Real.pi ≤ (1 / (314 / 100) : ℝ) :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith [Real.pi_gt_d2])
    have hb : (617 / 1000 : ℝ) ≤ 1 - 1 / Real.pi - d₀ := by linarith
    have hbase : (617 / 1000 : ℝ) * h ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_left hbranch]
      nlinarith [mul_le_mul_of_nonneg_left hb (le_of_lt hh0)]
    have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (le_trans (by positivity : (0 : ℝ) ≤ (617 / 1000 : ℝ) * h) hbase) 3)
    apply le_trans (min_le_left _ _) _
    change (134 / 1000 : ℝ) * h ^ 3 ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc, pow_pos hh0 3]
  · have hbranch' : (24 / 25 : ℝ) / h ≤ 1 - 1 / Real.pi := le_of_not_ge hbranch
    have hprod : h * d₀ ≤ (81 / 50 : ℝ) * (6363 / 100000 : ℝ) :=
      mul_le_mul hh.2 hd hd0 (by norm_num)
    have hbase : (856 / 1000 : ℝ) ≤ h * (u h - d₀) := by
      dsimp [u]
      rw [min_eq_right hbranch']
      have heq : h * ((24 / 25 : ℝ) / h - d₀) = 24 / 25 - h * d₀ := by
        field_simp
      rw [heq]
      linarith
    have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 856 / 1000) hbase 3
    have hm := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 574 / 1000)
    have hmc := mul_le_mul_of_nonneg_right (le_of_lt hc)
      (pow_nonneg (by linarith : 0 ≤ h * (u h - d₀)) 3)
    apply le_trans (min_le_right _ _) _
    change (36 / 100 : ℝ) ≤ _ * (h * (u h - d₀)) ^ 3
    nlinarith only [hm, hmc]

end CubicTorus.Shape

namespace CubicTorus.NestingGain
open CubicTorus.Nesting CubicTorus.Shape

lemma continuousOn_weight : ContinuousOn weight (Ici 0) := by
  exact Nesting.continuousOn_rawWeight.comp
    (continuous_id.min continuous_const).continuousOn
    (fun x hx => ⟨le_min hx (le_of_lt cutoff_pos), min_le_right _ _⟩)

lemma nesting_parameters {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    h * (u h - δ + δ * q) ∈ Icc 0 (24 / 25 : ℝ) ∧
      0 ≤ c * δ ^ 2 * shape q ∧ 1 + c * δ ^ 2 * shape q ≤ p₂ := by
  have hu := interval_placement hh
  have hh0 : 0 ≤ h := by linarith [hh.1]
  have hv0 : 0 ≤ u h - δ + δ * q := by
    have := mul_nonneg hδ.1 hq.1
    linarith [hu.2.1, hδ.2]
  have hv1 : u h - δ + δ * q ≤ u h := by
    have := mul_le_mul_of_nonneg_left hq.2 hδ.1
    linarith
  have hK0 : 0 ≤ c * δ ^ 2 * shape q := by
    exact mul_nonneg (mul_nonneg (by norm_num [c]) (sq_nonneg δ)) (shape_nonneg hq)
  have hK1 : c * δ ^ 2 * shape q ≤ c * dm ^ 2 * theta ^ 2 := by
    apply mul_le_mul (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hδ.1 hδ.2 2) (by norm_num [c])) (shape_max hq)
      (shape_nonneg hq) (by norm_num [c, dm])
  exact ⟨⟨mul_nonneg hh0 hv0,
    le_trans (mul_le_mul_of_nonneg_left hv1 hh0) hu.2.2.2.2.2⟩,
    hK0, by dsimp [p₂]; linarith⟩

lemma pointwise_uniform_gain {h δ q : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ))
    (hδ : δ ∈ Icc 0 dm) (hq : q ∈ Icc 0 1) :
    ((91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3) *
        ((u h - δ + δ * q) ^ 3 * shape q) ≤
      weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
        weight (h * (u h - δ + δ * q)) := by
  have hp := nesting_parameters hh hδ hq
  have hlow := pointwise_weight_gain hp.1 hp.2.1
  apply le_trans _ hlow
  have hnum : 0 ≤ (91 / 100 : ℝ) * (h * (u h - δ + δ * q)) ^ 3 *
      (c * δ ^ 2 * shape q) :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hp.1.1 3)) hp.2.1
  have hden : (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 ≤ Real.sqrt p₂ ^ 3 :=
    pow_le_pow_left₀ (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hp.2.2) 3
  have hden0 : 0 < (Real.sqrt (1 + c * δ ^ 2 * shape q)) ^ 3 := by
    apply pow_pos
    apply Real.sqrt_pos.2
    linarith [hp.2.1]
  convert div_le_div_of_nonneg_left hnum hden0 hden using 1
  all_goals try with_reducible_and_instances rfl
  ring

theorem integrated_uniform_gain_oai {h δ : ℝ}
    (hh : h ∈ Icc (51 / 50 : ℝ) (81 / 50 : ℝ)) (hδ : δ ∈ Icc 0 dm) :
    min ((134 / 1000 : ℝ) * h ^ 3) (36 / 100 : ℝ) * δ ^ 3 ≤
      δ * ∫ q in (0 : ℝ)..1,
        (weight ((h * (u h - δ + δ * q)) / Real.sqrt (1 + c * δ ^ 2 * shape q)) -
          weight (h * (u h - δ + δ * q))) := by
  let v : ℝ → ℝ := fun q => u h - δ + δ * q
  let K : ℝ → ℝ := fun q => c * δ ^ 2 * shape q
  have hv : Continuous v := by dsimp [v]; fun_prop
  have hK : Continuous K := by dsimp [K]; exact continuous_const.mul continuous_shape
  have hc1 : ContinuousOn (fun q => weight ((h * v q) / Real.sqrt (1 + K q))) (Icc 0 1) := by
    apply continuousOn_weight.comp
    · apply (continuous_const.mul hv).continuousOn.div
        (Real.continuous_sqrt.comp (continuous_const.add hK)).continuousOn
      intro q hq
      exact ne_of_gt (Real.sqrt_pos.2 (by
        change 0 < 1 + c * δ ^ 2 * shape q
        linarith [(nesting_parameters hh hδ hq).2.1]))
    · intro q hq
      exact div_nonneg (nesting_parameters hh hδ hq).1.1 (Real.sqrt_nonneg _)
  have hc2 : ContinuousOn (fun q => weight (h * v q)) (Icc 0 1) :=
    continuousOn_weight.comp (continuous_const.mul hv).continuousOn
      (fun q hq => (nesting_parameters hh hδ hq).1.1)
  have hright : IntervalIntegrable (fun q => weight ((h * v q) / Real.sqrt (1 + K q)) -
      weight (h * v q)) volume 0 1 :=
    ContinuousOn.intervalIntegrable_of_Icc (by norm_num) (hc1.sub hc2)
  let A : ℝ := (91 / 100 : ℝ) * c * δ ^ 2 * h ^ 3 / Real.sqrt p₂ ^ 3
  have hleft : IntervalIntegrable (fun q => A * (v q ^ 3 * shape q)) volume 0 1 :=
    (continuous_const.mul ((hv.pow 3).mul continuous_shape)).intervalIntegrable 0 1
  have hmon := intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    hleft hright (fun q hq => pointwise_uniform_gain hh hδ hq)
  rw [intervalIntegral.integral_const_mul] at hmon
  have hA : 0 ≤ A := by
    have hh0 : 0 ≤ h := by linarith [hh.1]
    dsimp [A, c]
    positivity
  have hu : dm ≤ u h := by linarith [(interval_placement hh).2.1]
  have hcubic := mul_le_mul_of_nonneg_left (cubic_shape_lower_dm hδ hu) hA
  have hδlower := mul_le_mul_of_nonneg_left (le_trans hcubic hmon) hδ.1
  have hcoeff := mul_le_mul_of_nonneg_right (uniform_coefficient hh) (pow_nonneg hδ.1 3)
  apply le_trans hcoeff
  convert hδlower using 1
  all_goals try with_reducible_and_instances rfl
  dsimp [A, v, K]
  ring

end CubicTorus.NestingGain

end
end
end

end

end OAI
end

theorem solution : type_of% @OAI.CubicTorus.NestingGain.integrated_uniform_gain_oai := @OAI.CubicTorus.NestingGain.integrated_uniform_gain_oai
