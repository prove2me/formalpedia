-- Prove2me | solution 1 for Komlos.gaussian_planar_comparison
-- status  : ACCEPTED   (prove)
-- author  : @Wenqian Xing
-- created : 2026-09-06T10:34:30.182806+00:00
-- url     : https://prove2.me/submissions/dd20fb3a-70c3-4dfb-bd77-0b9653a5f193

import Definitions.Def_Komlos_gaussian_fold_analysis
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic

/-!
Gaussian tail comparisons for the folding proof in Garg (2018), Chapter 3.
Adapted portions: Copyright (c) 2026 Asher Yan. All rights reserved.
Released under the Apache License, Version 2.0: https://www.apache.org/licenses/LICENSE-2.0 .
Authors of the referenced file: Asher Yan with ChatGPT 5.6.
Changes: adapted derivative and improper-integral helpers to the kernel notation,
then added hazard comparisons, certified numerical bounds, and planar integration.

The elementary derivative / improper-integral approach to the Mills bound was
adapted from Asher Yan's Apache-2.0 ProbabilityApproximation, file
Stein/IndicatorSolution.lean, commit a2fc5bda874d9b69186c0ba165bf79f3b9897662.
The hazard and translated interval comparisons below are developed here.
-/

open MeasureTheory Real Set Filter
open scoped Topology intervalIntegral

namespace GaussianFoldAnalysis


lemma kernel_pos (x : ℝ) : 0 < kernel x := exp_pos _

lemma integrable_kernel : Integrable kernel := by
  convert integrable_exp_neg_mul_sq (by positivity : (0 : ℝ) < 1 / 2) using 1
  ext x
  unfold kernel
  ring_nf

lemma continuous_kernel : Continuous kernel := by unfold kernel; fun_prop

lemma hasDerivAt_kernel (x : ℝ) : HasDerivAt kernel (-x * kernel x) x := by
  have hp : HasDerivAt (fun u : ℝ => -u ^ 2 / 2) (-x) x := by
    exact ((hasDerivAt_pow 2 x).neg.div_const (2 : ℝ)).congr_deriv (by norm_num; ring)
  exact hp.exp.congr_deriv (by unfold kernel; ring)

lemma tendsto_kernel : Tendsto kernel atTop (𝓝 0) := by
  have hsq : Tendsto (fun b : ℝ => b ^ 2) atTop atTop := by
    simpa [pow_two] using (tendsto_mul_self_atTop (α := ℝ))
  have hhalf := hsq.atTop_div_const (by positivity : (0 : ℝ) < 2)
  have hbot : Tendsto (fun b : ℝ => -b ^ 2 / 2) atTop atBot := by
    refine (tendsto_neg_atTop_atBot.comp hhalf).congr ?_
    intro b
    simp [neg_div]
  exact tendsto_exp_atBot.comp hbot

lemma tail_pos (x : ℝ) : 0 < tail x := by
  unfold tail
  apply (setIntegral_pos_iff_support_of_nonneg_ae
    (ae_of_all _ fun t => (kernel_pos t).le) integrable_kernel.integrableOn).2
  have hs : Function.support kernel = univ := by
    ext t
    simp [Function.mem_support, ne_of_gt (kernel_pos t)]
  simp [hs]

lemma hasDerivAt_tail (x : ℝ) : HasDerivAt tail (-kernel x) x := by
  have hpoint (u : ℝ) : tail u = tail x - ∫ t in x..u, kernel t := by
    have := intervalIntegral.integral_Ioi_sub_Ioi'
      (a := x) (b := u) integrable_kernel.integrableOn integrable_kernel.integrableOn
    change tail x - tail u = _ at this
    linarith
  have hFTC : HasDerivAt (fun u => ∫ t in x..u, kernel t) (kernel x) x :=
    intervalIntegral.integral_hasDerivAt_right integrable_kernel.intervalIntegrable
      integrable_kernel.aestronglyMeasurable.stronglyMeasurableAtFilter
      continuous_kernel.continuousAt
  exact (((hasDerivAt_const x (tail x)).sub hFTC).congr_of_eventuallyEq
    (Eventually.of_forall hpoint)).congr_deriv (by ring)

lemma mills_bound (x : ℝ) : x * tail x ≤ kernel x := by
  by_cases hx : 0 ≤ x
  · have hd : ∀ t ∈ Ici x, HasDerivAt (fun u => -kernel u) (t * kernel t) t := by
      intro t _
      exact (hasDerivAt_kernel t).neg.congr_deriv (by ring)
    have hp : ∀ t ∈ Ioi x, 0 ≤ t * kernel t :=
      fun t ht => mul_nonneg (hx.trans ht.le) (kernel_pos t).le
    have hl : Tendsto (fun t => -kernel t) atTop (𝓝 0) := by
      simpa using tendsto_kernel.neg
    have hi := integrableOn_Ioi_deriv_of_nonneg' hd hp hl
    have he := integral_Ioi_of_hasDerivAt_of_nonneg' hd hp hl
    have hm := setIntegral_mono_on (integrable_kernel.integrableOn.const_mul x) hi
      measurableSet_Ioi (fun t ht => mul_le_mul_of_nonneg_right ht.le (kernel_pos t).le)
    rw [integral_const_mul] at hm
    change x * tail x ≤ _ at hm
    linarith
  · exact (mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hx) (tail_pos x).le).trans
      (kernel_pos x).le

noncomputable def hazard (x : ℝ) : ℝ := kernel x / tail x

lemma hasDerivAt_hazard (x : ℝ) :
    HasDerivAt hazard (kernel x * (kernel x - x * tail x) / tail x ^ 2) x := by
  exact ((hasDerivAt_kernel x).div (hasDerivAt_tail x)
    (ne_of_gt (tail_pos x))).congr_deriv (by ring)

lemma monotone_hazard : Monotone hazard := by
  apply monotone_of_hasDerivAt_nonneg hasDerivAt_hazard
  intro x
  exact div_nonneg (mul_nonneg (kernel_pos x).le (sub_nonneg.mpr (mills_bound x)))
    (sq_nonneg _)

lemma antitone_tail : Antitone tail :=
  antitone_of_hasDerivAt_nonpos hasDerivAt_tail (fun x => neg_nonpos.mpr (kernel_pos x).le)

lemma antitone_tail_ratio (r : ℝ) (hr : 0 ≤ r) :
    Antitone (fun x => tail (x + r) / tail x) := by
  apply antitone_of_hasDerivAt_nonpos
    (fun x => ((hasDerivAt_tail (x + r)).comp x ((hasDerivAt_id x).add_const r)).div
      (hasDerivAt_tail x) (ne_of_gt (tail_pos x)))
  intro x
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hm := monotone_hazard (show x ≤ x + r by linarith)
  change kernel x / tail x ≤ kernel (x + r) / tail (x + r) at hm
  have hm' := (div_le_div_iff₀ (tail_pos x) (tail_pos (x + r))).mp hm
  dsimp
  nlinarith

lemma monotone_interval_tail_ratio (r q : ℝ) (hr : 0 ≤ r) (hq : 0 ≤ q) :
    Monotone (fun x => (∫ t in x..x + r, kernel t) / tail (x + q)) := by
  intro x y hxy
  have hR := antitone_tail_ratio r hr hxy
  have hQ := antitone_tail_ratio q hq hxy
  have hB : 0 ≤ 1 - tail (y + r) / tail y := by
    apply sub_nonneg.mpr
    apply (div_le_one (tail_pos y)).mpr
    exact antitone_tail (by linarith)
  have hiQ : 1 / (tail (x + q) / tail x) ≤ 1 / (tail (y + q) / tail y) :=
    one_div_le_one_div_of_le (div_pos (tail_pos (y + q)) (tail_pos y)) hQ
  have hm := mul_le_mul (sub_le_sub_left hR 1) hiQ
    (le_of_lt (one_div_pos.mpr (div_pos (tail_pos (x + q)) (tail_pos x)))) hB
  have hi (z : ℝ) : (∫ t in z..z + r, kernel t) / tail (z + q) =
      (1 - tail (z + r) / tail z) * (1 / (tail (z + q) / tail z)) := by
    rw [← intervalIntegral.integral_Ioi_sub_Ioi' integrable_kernel.integrableOn
      integrable_kernel.integrableOn]
    change (tail z - tail (z + r)) / tail (z + q) = _
    field_simp [ne_of_gt (tail_pos z), ne_of_gt (tail_pos (z + q))]
  change (∫ t in x..x + r, kernel t) / tail (x + q) ≤
    (∫ t in y..y + r, kernel t) / tail (y + q)
  rw [hi x, hi y]
  exact hm


lemma hasDerivAt_double_tail_ratio (x : ℝ) :
    HasDerivAt (fun t => tail t ^ 2 / tail (2 * t))
      (2 * tail x * (tail x * kernel (2 * x) - kernel x * tail (2 * x)) /
        tail (2 * x) ^ 2) x := by
  exact (((hasDerivAt_tail x).pow 2).div
    ((hasDerivAt_tail (2 * x)).comp x ((hasDerivAt_id x).const_mul 2))
    (ne_of_gt (tail_pos (2 * x)))).congr_deriv (by norm_num; ring)

lemma monotoneOn_double_tail_ratio :
    MonotoneOn (fun x => tail x ^ 2 / tail (2 * x)) (Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
    ((fun x => (hasDerivAt_double_tail_ratio x).continuousAt) |> continuous_iff_continuousAt.mpr).continuousOn
    ((fun x => (hasDerivAt_double_tail_ratio x).differentiableAt) |> Differentiable.differentiableOn)
  intro x hx
  rw [(hasDerivAt_double_tail_ratio x).deriv]
  have hx0 : 0 ≤ x := (interior_subset hx)
  have hm := monotone_hazard (show x ≤ 2 * x by linarith)
  change kernel x / tail x ≤ kernel (2 * x) / tail (2 * x) at hm
  have hm' := (div_le_div_iff₀ (tail_pos x) (tail_pos (2 * x))).mp hm
  exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (tail_pos x).le)
    (sub_nonneg.mpr (by nlinarith))) (sq_nonneg _)

private lemma exp_taylor16 (x : ℝ) (hx : |x| ≤ 2) :
    |exp x - ∑ i ∈ Finset.range 16, x ^ i / (i.factorial : ℝ)| ≤ 1 / 10000000 := by
  have h := Complex.exp_bound' (x := (x : ℂ)) (n := 16) (by
    rw [Complex.norm_real, Real.norm_eq_abs]
    norm_num
    linarith)
  have he : |exp x - ∑ i ∈ Finset.range 16, x ^ i / (i.factorial : ℝ)| ≤
      |x| ^ 16 / ((Nat.factorial 16) : ℝ) * 2 := by
    convert h using 1 <;> norm_cast
  refine he.trans ?_
  calc
    |x| ^ 16 / ((Nat.factorial 16) : ℝ) * 2 ≤ 2 ^ 16 / ((Nat.factorial 16) : ℝ) * 2 := by gcongr
    _ ≤ 1 / 10000000 := by norm_num

noncomputable def poly (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 16, (-1 / 2 : ℝ) ^ i / (i.factorial : ℝ) * t ^ (2 * i)
noncomputable def prim (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range 16, (-1 / 2 : ℝ) ^ i / (i.factorial : ℝ) *
    t ^ (2 * i + 1) / (2 * i + 1 : ℕ)

lemma kernel_poly_bound (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |kernel t - poly t| ≤ 1 / 10000000 := by
  have ht : |-t ^ 2 / 2| ≤ 2 := by
    rw [abs_of_nonpos (by nlinarith [sq_nonneg t] : -t ^ 2 / 2 ≤ 0)]
    nlinarith
  have hp : poly t = ∑ i ∈ Finset.range 16, (-t ^ 2 / 2) ^ i / (i.factorial : ℝ) := by
    apply Finset.sum_congr rfl
    intro i _
    have he : -t ^ 2 / 2 = (-1 / 2 : ℝ) * t ^ 2 := by ring
    rw [he, mul_pow, ← pow_mul]
    ring
  rw [hp]
  exact exp_taylor16 _ ht

lemma integral_poly (t : ℝ) : (∫ x in 0..t, poly x) = prim t := by
  unfold poly prim
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [intervalIntegral.integral_const_mul, integral_pow]
    simp only [zero_pow (by omega : 2 * i + 1 ≠ 0), sub_zero]
    push_cast
    ring
  · intro i _
    exact (by fun_prop : Continuous (fun x : ℝ =>
      (-1 / 2 : ℝ) ^ i / (i.factorial : ℝ) * x ^ (2 * i))).intervalIntegrable _ _

lemma integral_kernel_approx (t : ℝ) (ht0 : 0 ≤ t) (ht2 : t ≤ 2) :
    |(∫ x in 0..t, kernel x) - prim t| ≤ 1 / 5000000 := by
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := t) (f := fun x => kernel x - poly x) (C := 1 / 10000000)
    (fun x hx => by
      rw [Real.norm_eq_abs]
      rw [uIoc_of_le ht0] at hx
      exact kernel_poly_bound x hx.1.le (hx.2.trans ht2))
  rw [intervalIntegral.integral_sub integrable_kernel.intervalIntegrable
    (by exact (by unfold poly; fun_prop : Continuous poly).intervalIntegrable _ _),
    integral_poly, Real.norm_eq_abs, sub_zero, abs_of_nonneg ht0] at hi
  exact hi.trans (by linarith)

lemma tail_zero_value : tail 0 = sqrt (2 * π) / 2 := by
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  convert h using 1
  · unfold tail kernel
    congr 1
    ext x
    congr 1
    ring
  · congr 2
    ring

lemma tail_zero_bounds : (1253314 / 1000000 : ℝ) < tail 0 ∧
    tail 0 < (1253315 / 1000000 : ℝ) := by
  rw [tail_zero_value]
  have hs := sq_sqrt (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) pi_pos.le)
  have hp := pi_gt_d6
  have hq := pi_lt_d6
  have hn := sqrt_nonneg (2 * π)
  constructor <;> nlinarith

lemma numerical_tail_bounds :
    (397689 / 1000000 : ℝ) < tail 1 ∧ tail 2 < (57028 / 1000000 : ℝ) ∧
    (∫ x in (0 : ℝ)..(1 / 5 : ℝ), kernel x) < (198676 / 1000000 : ℝ) := by
  have h1 := integral_kernel_approx 1 (by norm_num) (by norm_num)
  have h2 := integral_kernel_approx 2 (by norm_num) (by norm_num)
  have hr := integral_kernel_approx (1 / 5) (by norm_num) (by norm_num)
  have hz := tail_zero_bounds
  have hi (x : ℝ) : tail 0 - tail x = ∫ t in (0 : ℝ)..x, kernel t :=
    intervalIntegral.integral_Ioi_sub_Ioi' integrable_kernel.integrableOn integrable_kernel.integrableOn
  rw [← hi] at h1 h2
  norm_num [prim, Finset.sum_range_succ] at h1 h2 hr
  rcases abs_le.mp h1 with ⟨h1l, h1u⟩
  rcases abs_le.mp h2 with ⟨h2l, h2u⟩
  rcases abs_le.mp hr with ⟨hrl, hru⟩
  constructor
  · linarith [hz.1]
  constructor
  · linarith [hz.2]
  · linarith



lemma intervalMass_nonneg (r x : ℝ) (hr : 0 ≤ r) : 0 ≤ intervalMass r x := by
  apply intervalIntegral.integral_nonneg (by linarith)
  intro t _
  exact (kernel_pos t).le

lemma intervalMass_reflect (r t : ℝ) (hr : 0 ≤ r) (ht : 0 ≤ t) :
    intervalMass r t ≤ intervalMass r (-t) := by
  have hc (s : ℝ) : intervalMass r s = ∫ y in (0 : ℝ)..r, kernel (s + y) := by
    rw [intervalIntegral.integral_comp_add_left]
    simp [intervalMass]
  rw [hc t, hc (-t)]
  apply intervalIntegral.integral_mono_on hr
    ((continuous_kernel.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
    ((continuous_kernel.comp (continuous_const.add continuous_id)).intervalIntegrable _ _)
  intro y hy
  apply exp_le_exp.mpr
  change -(t + y) ^ 2 / 2 ≤ -(-t + y) ^ 2 / 2
  nlinarith [mul_nonneg ht hy.1]

lemma half_tail_le_interval (r a t : ℝ) (hr : 0 ≤ r) (ha : 0 ≤ a) (ht : 0 ≤ t)
    (hbase : tail a ≤ 2 * intervalMass r 0) :
    tail (t + a) / 2 ≤ intervalMass r t ∧
    tail (t + a) / 2 ≤ intervalMass r (-t) := by
  have hm := monotone_interval_tail_ratio r a hr ha ht
  change intervalMass r 0 / tail (0 + a) ≤ intervalMass r t / tail (t + a) at hm
  rw [zero_add] at hm
  have hl : (1 / 2 : ℝ) ≤ intervalMass r 0 / tail a :=
    (le_div_iff₀ (tail_pos a)).mpr (by linarith)
  have hf := (le_div_iff₀ (tail_pos (t + a))).mp (hl.trans hm)
  have hf' : tail (t + a) / 2 ≤ intervalMass r t := by linarith
  exact ⟨hf', hf'.trans (intervalMass_reflect r t hr ht)⟩

lemma tail_one_constants :
    2 * intervalMass (1 / 5) 0 < tail 1 ∧
    2 * tail 0 * tail 2 < tail 1 ^ 2 := by
  rcases numerical_tail_bounds with ⟨h1, h2, hr⟩
  have hz := tail_zero_bounds
  have h0p := tail_pos 0
  have h1p := tail_pos 1
  have h2p := tail_pos 2
  constructor
  · simpa only [intervalMass, zero_add] using (show
      2 * (∫ x in (0 : ℝ)..(1 / 5 : ℝ), kernel x) < tail 1 by linarith)
  · have hm := mul_lt_mul_of_pos_left h2 (by linarith : 0 < 2 * tail 0)
    have hn := mul_lt_mul_of_pos_right hz.2 (by norm_num : (0 : ℝ) < 2 * (57028 / 1000000))
    nlinarith [sq_nonneg (tail 1 - 397689 / 1000000)]

lemma threshold_ge_one (r a : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 5)
    (hbase : tail a ≤ 2 * intervalMass r 0) : 1 ≤ a := by
  by_contra ha
  have hm := antitone_tail (le_of_not_ge ha)
  have hi : intervalMass r 0 ≤ intervalMass (1 / 5) 0 := by
    simp only [intervalMass, zero_add]
    exact intervalIntegral.integral_mono_interval le_rfl hr hrsmall
      (ae_of_all _ fun x => (kernel_pos x).le) integrable_kernel.intervalIntegrable
  have hn := tail_one_constants.1
  linarith

lemma full_tail_le_interval (r a t : ℝ) (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 5)
    (hbase : tail a ≤ 2 * intervalMass r 0) (ht : a ≤ t) :
    tail (t + a) ≤ intervalMass r t := by
  have ha := threshold_ge_one r a hr hrsmall hbase
  have ha0 : 0 ≤ a := by linarith
  have hz := tail_pos 0
  have haP := tail_pos a
  have h2aP := tail_pos (2 * a)
  have h2P := tail_pos 2
  have hn := tail_one_constants.2.le
  have hd := monotoneOn_double_tail_ratio (show (1 : ℝ) ∈ Ici 0 by norm_num) ha0 ha
  change tail 1 ^ 2 / tail (2 * 1) ≤ tail a ^ 2 / tail (2 * a) at hd
  rw [mul_one] at hd
  have hn' : 2 * tail 0 ≤ tail 1 ^ 2 / tail 2 := (le_div_iff₀ h2P).mpr hn
  have hsq := (le_div_iff₀ h2aP).mp (hn'.trans hd)
  have hi := monotone_interval_tail_ratio r 0 hr le_rfl ha0
  change intervalMass r 0 / tail (0 + 0) ≤ intervalMass r a / tail (a + 0) at hi
  simp only [add_zero] at hi
  have hi' := (div_le_div_iff₀ hz haP).mp hi
  have hb : tail (2 * a) ≤ intervalMass r a := by
    nlinarith [mul_le_mul_of_nonneg_right hbase haP.le]
  have hf := monotone_interval_tail_ratio r a hr ha0 ht
  change intervalMass r a / tail (a + a) ≤ intervalMass r t / tail (t + a) at hf
  rw [← two_mul a] at hf
  have hstart : (1 : ℝ) ≤ intervalMass r a / tail (2 * a) :=
    (one_le_div h2aP).mpr hb
  simpa only [one_mul] using (le_div_iff₀ (tail_pos (t + a))).mp (hstart.trans hf)


lemma continuous_tail : Continuous tail :=
  continuous_iff_continuousAt.mpr (fun x => (hasDerivAt_tail x).continuousAt)

lemma continuous_intervalMass (r : ℝ) : Continuous (intervalMass r) := by
  have he : intervalMass r = fun x => tail x - tail (x + r) := by
    funext x
    exact (intervalIntegral.integral_Ioi_sub_Ioi'
      integrable_kernel.integrableOn integrable_kernel.integrableOn).symm
  rw [he]
  exact continuous_tail.sub (continuous_tail.comp (continuous_id.add continuous_const))

lemma intervalMass_norm_le (r x : ℝ) (hr : 0 ≤ r) : ‖intervalMass r x‖ ≤ r := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := x) (b := x + r) (f := kernel) (C := 1) (fun t _ => by
      rw [Real.norm_eq_abs, abs_of_pos (kernel_pos t)]
      apply exp_le_one_iff.mpr
      nlinarith [sq_nonneg t])
  simpa only [intervalMass, add_sub_cancel_left, abs_of_nonneg hr, one_mul] using h

lemma integrable_weighted_interval (r : ℝ) (hr : 0 ≤ r)
    (f v : ℝ → ℝ) (hf : Integrable f) (hv : Continuous v) :
    Integrable (fun x => f x * intervalMass r (v x)) :=
  hf.mul_bdd ((continuous_intervalMass r).comp hv).aestronglyMeasurable
    (ae_of_all _ fun x => intervalMass_norm_le r (v x) hr)

lemma kernel_weight_comparisons (w d x : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hx : 0 ≤ x) :
    kernel (w + d + x) ≤ kernel (w + x) ∧
    kernel (w + d + x) ≤ kernel (w - x) := by
  constructor <;> apply exp_le_exp.mpr
  · change -(w + d + x) ^ 2 / 2 ≤ -(w + x) ^ 2 / 2
    nlinarith [mul_nonneg hd (show 0 ≤ 2 * w + d + 2 * x by linarith)]
  · change -(w + d + x) ^ 2 / 2 ≤ -(w - x) ^ 2 / 2
    nlinarith [mul_nonneg (show 0 ≤ d + 2 * x by linarith)
      (show 0 ≤ 2 * w + d by linarith)]

/-- The complete planar Gaussian comparison, in translated and reflected coordinates. -/
lemma planar_comparison (w d b r : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 5)
    (hbase : tail (b * d) ≤ 2 * intervalMass r 0) :
    (∫ x in Ioi (0 : ℝ), kernel (w + d + x) * tail (b * (d + x))) ≤
      (∫ x in Ioi (0 : ℝ), kernel (w - x) * intervalMass r (b * x)) +
      ∫ x in (0 : ℝ)..d, kernel (w + x) * intervalMass r (-b * x) := by
  let B : ℝ → ℝ := fun x => kernel (w + d + x) * tail (b * (d + x))
  let M : ℝ → ℝ := fun x => kernel (w - x) * intervalMass r (b * x)
  let P : ℝ → ℝ := fun x => kernel (w + x) * intervalMass r (-b * x)
  have cB : Continuous B := continuous_kernel.comp (by fun_prop) |>.mul
    (continuous_tail.comp (by fun_prop))
  have cM : Continuous M := continuous_kernel.comp (by fun_prop) |>.mul
    ((continuous_intervalMass r).comp (by fun_prop))
  have cP : Continuous P := continuous_kernel.comp (by fun_prop) |>.mul
    ((continuous_intervalMass r).comp (by fun_prop))
  have iM : Integrable M := integrable_weighted_interval r hr _ _
    (integrable_kernel.comp_sub_left w) (by fun_prop)
  have iB : IntegrableOn B (Ioi 0) := by
    refine Integrable.mono' ((integrable_kernel.comp_add_left (w + d)).integrableOn.mul_const
      (tail 0)) cB.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [Real.norm_eq_abs]
    change |kernel (w + d + x) * tail (b * (d + x))| ≤ _
    rw [abs_of_pos (mul_pos (kernel_pos _) (tail_pos _))]
    exact mul_le_mul_of_nonneg_left
      (antitone_tail (mul_nonneg hb (add_nonneg hd hx.le))) (kernel_pos _).le
  have hnear (x : ℝ) (hx : 0 ≤ x) : B x ≤ M x + P x := by
    have h := half_tail_le_interval r (b * d) (b * x) hr (mul_nonneg hb hd)
      (mul_nonneg hb hx) hbase
    have he : b * x + b * d = b * (d + x) := by ring
    rw [he] at h
    have hweights := kernel_weight_comparisons w d x hw hd hx
    have hm : B x / 2 ≤ M x := by
      have hi := mul_le_mul_of_nonneg_left h.1 (kernel_pos (w + d + x)).le
      have hj := mul_le_mul_of_nonneg_right hweights.2 (intervalMass_nonneg r (b * x) hr)
      dsimp [B, M]
      nlinarith
    have hp : B x / 2 ≤ P x := by
      have hi := mul_le_mul_of_nonneg_left h.2 (kernel_pos (w + d + x)).le
      have hj := mul_le_mul_of_nonneg_right hweights.1 (intervalMass_nonneg r (-b * x) hr)
      rw [neg_mul] at hj
      dsimp [B, P]
      rw [neg_mul]
      nlinarith
    linarith
  have hfar (x : ℝ) (hx : d ≤ x) : B x ≤ M x := by
    have h := full_tail_le_interval r (b * d) (b * x) hr hrsmall hbase
      (mul_le_mul_of_nonneg_left hx hb)
    have he : b * x + b * d = b * (d + x) := by ring
    rw [he] at h
    exact (mul_le_mul_of_nonneg_left h (kernel_pos (w + d + x)).le).trans
      (mul_le_mul_of_nonneg_right (kernel_weight_comparisons w d x hw hd (hd.trans hx)).2
        (intervalMass_nonneg r (b * x) hr))
  have iBd : IntegrableOn B (Ioi d) := iB.mono_set (Ioi_subset_Ioi hd)
  have hn : (∫ x in (0 : ℝ)..d, B x) ≤ ∫ x in (0 : ℝ)..d, M x + P x :=
    intervalIntegral.integral_mono_on hd (cB.intervalIntegrable _ _)
      ((cM.add cP).intervalIntegrable _ _) (fun x hx => hnear x hx.1)
  rw [intervalIntegral.integral_add (cM.intervalIntegrable _ _) (cP.intervalIntegrable _ _)] at hn
  have hf := setIntegral_mono_on iBd iM.integrableOn measurableSet_Ioi
    (fun x hx => hfar x hx.le)
  have eB := intervalIntegral.integral_interval_add_Ioi iB iBd
  have eM := intervalIntegral.integral_interval_add_Ioi
    (a := 0) (b := d) iM.integrableOn iM.integrableOn
  change (∫ x in Ioi (0 : ℝ), B x) ≤ (∫ x in Ioi (0 : ℝ), M x) + ∫ x in (0 : ℝ)..d, P x
  linarith

end GaussianFoldAnalysis

open GaussianFoldAnalysis

theorem solution (w d b r : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hb : 0 ≤ b)
    (hr : 0 ≤ r) (hrsmall : r ≤ 1 / 5)
    (hbase : tail (b * d) ≤ 2 * intervalMass r 0) :
    (∫ x in Ioi (0 : ℝ), kernel (w + d + x) * tail (b * (d + x))) ≤
      (∫ x in Ioi (0 : ℝ), kernel (w - x) * intervalMass r (b * x)) +
      ∫ x in (0 : ℝ)..d, kernel (w + x) * intervalMass r (-b * x) :=
  planar_comparison w d b r hw hd hb hr hrsmall hbase

#print axioms solution
