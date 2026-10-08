-- Prove2me | solution 1 for KingmanSubadditive.Ulam.greedy_mean_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:12:17.900951+00:00
-- url     : https://prove2.me/submissions/4f682169-a8d4-41dd-a9cc-ad308f97fd59

import Mathlib
import Definitions.Def_KingmanSubadditive_Ulam_Permutations

open MeasureTheory Set


namespace KingmanSubadditive.Ulam

open Filter Topology Real

/-- the half-Gaussian integral -/
lemma gauss_half : ∫ y in Ioi (0 : ℝ), Real.exp (-y ^ 2 / 2) = Real.sqrt (Real.pi / 2) := by
  have h := integral_gaussian_Ioi (1 / 2 : ℝ)
  have h2 : (fun y : ℝ => Real.exp (-(1 / 2 : ℝ) * y ^ 2)) = fun y => Real.exp (-y ^ 2 / 2) := by
    funext y; ring_nf
  rw [h2] at h
  rw [h]
  rw [show Real.pi / (1 / 2) = 4 * (Real.pi / 2) by ring, Real.sqrt_mul (by norm_num),
    show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  ring

/-- pointwise bound: for `x, y ≥ 0`, `exp (-(x+y)^2/2) ≤ exp (-x^2/2)` -/
lemma exp_bound {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.exp (-(x + y) ^ 2 / 2) ≤ Real.exp (-x ^ 2 / 2) := by
  apply Real.exp_le_exp.2
  nlinarith

lemma exp_bound2 {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.exp (-(x + y) ^ 2 / 2) ≤ Real.exp (-x ^ 2 / 2) * Real.exp (-y ^ 2 / 2) := by
  rw [← Real.exp_add]
  apply Real.exp_le_exp.2
  nlinarith

/-- the derivative identity -/
lemma hasDerivAt_neg_exp (y x : ℝ) :
    HasDerivAt (fun x => -Real.exp (-(x + y) ^ 2 / 2)) ((x + y) * Real.exp (-(x + y) ^ 2 / 2)) x := by
  have h1 : HasDerivAt (fun x => -(x + y) ^ 2 / 2) (-(x + y)) x := by
    have := (((hasDerivAt_id x).add_const y).pow 2).neg.div_const 2
    refine (this.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
    · simp; ring
    · simp [Pi.pow_apply]
  have h3 := h1.exp.neg
  refine (h3.congr_deriv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun z => ?_)
  · ring
  · simp

/-- integrability of `exp (-(x+y)^2/2)` on `Ioi 0` for `y ≥ 0` -/
lemma integrable_shift (y : ℝ) (hy : 0 ≤ y) :
    IntegrableOn (fun x : ℝ => Real.exp (-(x + y) ^ 2 / 2)) (Ioi 0) := by
  have hg : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Ioi 0) := by
    have := (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn (s := Ioi 0)
    refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
    ring_nf
  refine hg.mono' ?_ ?_
  · exact (by fun_prop : Continuous fun x : ℝ => Real.exp (-(x + y) ^ 2 / 2)).aestronglyMeasurable
  · rw [ae_restrict_iff' measurableSet_Ioi]
    filter_upwards with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_bound (le_of_lt hx) hy

/-- the inner integral, via the fundamental theorem of calculus -/
lemma inner_integral (y : ℝ) (hy : 0 ≤ y) :
    ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      Real.exp (-y ^ 2 / 2) - y * ∫ x in Ioi (0 : ℝ), Real.exp (-(x + y) ^ 2 / 2) := by
  have hderiv : ∀ x ∈ Ioi (0 : ℝ), HasDerivAt (fun x => -Real.exp (-(x + y) ^ 2 / 2))
      ((x + y) * Real.exp (-(x + y) ^ 2 / 2)) x := fun x _ => hasDerivAt_neg_exp y x
  have hpos : ∀ x ∈ Ioi (0 : ℝ), 0 ≤ (x + y) * Real.exp (-(x + y) ^ 2 / 2) := by
    intro x hx
    have : (0 : ℝ) < x := hx
    positivity
  have hlim : Tendsto (fun x => -Real.exp (-(x + y) ^ 2 / 2)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun x : ℝ => (x + y) ^ 2 / 2) atTop atTop := by
      have := (tendsto_atTop_add_const_right atTop y tendsto_id)
      exact ((tendsto_pow_atTop two_ne_zero).comp this).atTop_div_const (by norm_num)
    have h2 : Tendsto (fun x : ℝ => Real.exp (-(x + y) ^ 2 / 2)) atTop (𝓝 0) := by
      have := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp h1)
      refine this.congr (fun x => ?_)
      simp only [Function.comp]; ring_nf
    simpa using h2.neg
  have hcont : ContinuousWithinAt (fun x => -Real.exp (-(x + y) ^ 2 / 2)) (Ici 0) 0 :=
    (by fun_prop : Continuous fun x : ℝ => -Real.exp (-(x + y) ^ 2 / 2)).continuousWithinAt
  have hint := integrableOn_Ioi_deriv_of_nonneg hcont hderiv hpos hlim
  have hval := integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hpos hlim
  simp only [zero_add, neg_neg, zero_sub] at hval
  have hshift := integrable_shift y hy
  have hsplit : ∀ x : ℝ, x * Real.exp (-(x + y) ^ 2 / 2) =
      (x + y) * Real.exp (-(x + y) ^ 2 / 2) - y * Real.exp (-(x + y) ^ 2 / 2) := by
    intro x; ring
  simp_rw [hsplit]
  rw [integral_sub hint (hshift.const_mul y), hval, integral_const_mul]


lemma integrable_gauss_half : IntegrableOn (fun x : ℝ => Real.exp (-x ^ 2 / 2)) (Ioi 0) := by
  have := (integrable_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn (s := Ioi 0)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  ring_nf

lemma integrable_x_gauss_half : IntegrableOn (fun x : ℝ => x * Real.exp (-x ^ 2 / 2)) (Ioi 0) := by
  have := (integrable_mul_exp_neg_mul_sq (b := (1 / 2 : ℝ)) (by norm_num)).integrableOn (s := Ioi 0)
  refine this.congr_fun (fun x _ => ?_) measurableSet_Ioi
  ring_nf

lemma integrable_prod_F :
    Integrable (fun z : ℝ × ℝ => z.1 * Real.exp (-(z.2 + z.1) ^ 2 / 2))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) := by
  have hg : Integrable (fun z : ℝ × ℝ => (z.1 * Real.exp (-z.1 ^ 2 / 2)) * Real.exp (-z.2 ^ 2 / 2))
      (((volume : Measure ℝ).restrict (Ioi 0)).prod ((volume : Measure ℝ).restrict (Ioi 0))) :=
    Integrable.mul_prod integrable_x_gauss_half integrable_gauss_half
  refine hg.mono' ?_ ?_
  · exact (by fun_prop :
      Continuous fun z : ℝ × ℝ => z.1 * Real.exp (-(z.2 + z.1) ^ 2 / 2)).aestronglyMeasurable
  · rw [Measure.prod_restrict, ae_restrict_iff' (measurableSet_Ioi.prod measurableSet_Ioi)]
    filter_upwards with z hz
    obtain ⟨hz1, hz2⟩ := hz
    have h1 : (0 : ℝ) < z.1 := hz1
    have h2 : (0 : ℝ) < z.2 := hz2
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    calc z.1 * Real.exp (-(z.2 + z.1) ^ 2 / 2)
        ≤ z.1 * (Real.exp (-z.2 ^ 2 / 2) * Real.exp (-z.1 ^ 2 / 2)) :=
          mul_le_mul_of_nonneg_left (exp_bound2 h2.le h1.le) h1.le
      _ = z.1 * Real.exp (-z.1 ^ 2 / 2) * Real.exp (-z.2 ^ 2 / 2) := by ring

theorem greedy_mean_integral_core :
    ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      Real.sqrt (Real.pi / 8) := by
  have hF := integrable_prod_F
  -- the function y ↦ y * J y
  have hJ : Integrable (fun y : ℝ => y * ∫ x in Ioi (0 : ℝ), Real.exp (-(x + y) ^ 2 / 2))
      ((volume : Measure ℝ).restrict (Ioi 0)) := by
    have := hF.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [integral_const_mul]
  have hswap : ∫ y in Ioi (0 : ℝ), y * ∫ x in Ioi (0 : ℝ), Real.exp (-(x + y) ^ 2 / 2) =
      ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) := by
    have h1 : ∀ y : ℝ, y * ∫ x in Ioi (0 : ℝ), Real.exp (-(x + y) ^ 2 / 2) =
        ∫ x in Ioi (0 : ℝ), y * Real.exp (-(x + y) ^ 2 / 2) := fun y => (integral_const_mul _ _).symm
    simp_rw [h1]
    rw [integral_integral_swap (f := fun y x => y * Real.exp (-(x + y) ^ 2 / 2)) hF]
    congr 1; funext x; congr 1; funext y; ring_nf
  have hsplit : ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      ∫ y in Ioi (0 : ℝ), (Real.exp (-y ^ 2 / 2) -
        y * ∫ x in Ioi (0 : ℝ), Real.exp (-(x + y) ^ 2 / 2)) :=
    setIntegral_congr_fun measurableSet_Ioi (fun y hy => inner_integral y (le_of_lt hy))
  set I := ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) with hI
  clear_value I
  rw [integral_sub integrable_gauss_half hJ, gauss_half, hswap] at hsplit
  have hI2 : I = Real.sqrt (Real.pi / 2) / 2 := by linarith
  rw [hI2, show Real.pi / 8 = Real.pi / 2 / 2 ^ 2 by ring,
    Real.sqrt_div' (Real.pi / 2) (by norm_num : (0 : ℝ) ≤ 2 ^ 2),
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

end KingmanSubadditive.Ulam

open KingmanSubadditive.Ulam


theorem solution :
    ∫ y in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), x * Real.exp (-(x + y) ^ 2 / 2) =
      Real.sqrt (Real.pi / 8) := by
  exact greedy_mean_integral_core
