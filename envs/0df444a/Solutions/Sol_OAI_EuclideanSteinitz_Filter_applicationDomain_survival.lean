-- Prove2me | solution 1 for OAI.EuclideanSteinitz.Filter.applicationDomain_survival
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-10-18T19:21:35.831469+00:00
-- url     : https://prove2.me/submissions/bb34e779-1650-4041-951d-f66fca99805b

import Mathlib
import Definitions.Def_OAIQWESB000
import Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_linear_image_finite_correlation
import Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_stdGaussian_closed_convex_correlation

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Compat
/-! Compatibility with the newer Lean core OpenAI's code was written against: lemmas it uses by
names this environment (Lean 4.33.1, Mathlib 0df444a) does not have yet. Each is the
corresponding `if_pos` / `if_neg` / `dif_pos` / `dif_neg`. -/
section OAICompat434
theorem ite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : p) :
    (if p then a else b) = a := if_pos h
theorem ite_eq_right {α : Sort _} {p : Prop} {_ : Decidable p} {a b : α} (h : ¬p) :
    (if p then a else b) = b := if_neg h
theorem dite_eq_left {α : Sort _} {p : Prop} {_ : Decidable p} {a : p → α} {b : ¬p → α} (h : p) :
    (if hp : p then a hp else b hp) = a h := dif_pos h
end OAICompat434
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.MatrixEnergy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar potentials and spectral endpoint inequalities. -/

namespace EuclideanSteinitz.MatrixEnergy

open Matrix
open scoped MatrixOrder

section Scalar

lemma exponent_pos : 0 < exponent := by norm_num [exponent]

lemma weight_of_le_one {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    weight x = x ^ exponent := by
  rcases hx.eq_or_lt with rfl | hx
  · norm_num [weight, exponent, Real.zero_rpow]
  apply min_eq_left
  exact (Real.rpow_le_one hx.le h1 exponent_pos.le).trans (one_le_inv₀ hx |>.mpr h1)

lemma weight_of_one_le {x : ℝ} (hx : 1 ≤ x) : weight x = x⁻¹ := by
  apply min_eq_right
  exact (inv_le_one₀ (by linarith : 0 < x) |>.mpr hx).trans
    (Real.one_le_rpow hx exponent_pos.le)

lemma integrand_of_le_one {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    weight x / x = x ^ (1 / 2 : ℝ) := by
  rw [weight_of_le_one hx h1]
  convert (Real.rpow_sub_one' hx (by norm_num [exponent] : exponent - 1 ≠ 0)).symm using 1
  norm_num [exponent]

lemma integrand_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    weight x / x = x ^ (-2 : ℝ) := by
  rw [weight_of_one_le hx]
  rw [show (-2 : ℝ) = -1 - 1 by norm_num,
    Real.rpow_sub_one (by linarith : x ≠ 0), Real.rpow_neg_one]

lemma potential_small {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    potential x = x ^ exponent / exponent := by
  unfold potential
  calc
    _ = ∫ u in (0 : ℝ)..x, u ^ (1 / 2 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hx] at hu
      exact integrand_of_le_one hu.1 (hu.2.trans h1)
    _ = _ := by
      rw [integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < 1 / 2))]
      norm_num [exponent]

lemma small_integrable {x : ℝ} (hx : 0 ≤ x) (h1 : x ≤ 1) :
    IntervalIntegrable (fun u => weight u / u) MeasureTheory.volume 0 x := by
  refine IntervalIntegrable.congr ?_
    (intervalIntegral.intervalIntegrable_rpow' (by norm_num : (-1 : ℝ) < 1 / 2))
  intro u hu
  rw [Set.uIoc_of_le hx] at hu
  exact (integrand_of_le_one hu.1.le (hu.2.trans h1)).symm

lemma large_integrable {x : ℝ} (hx : 1 ≤ x) :
    IntervalIntegrable (fun u => weight u / u) MeasureTheory.volume 1 x := by
  have hz : (0 : ℝ) ∉ Set.uIcc 1 x := by
    rw [Set.uIcc_of_le hx]
    simp
  refine IntervalIntegrable.congr ?_
    (intervalIntegral.intervalIntegrable_rpow (Or.inr hz) :
      IntervalIntegrable (fun u : ℝ => u ^ (-2 : ℝ)) MeasureTheory.volume 1 x)
  intro u hu
  rw [Set.uIoc_of_le hx] at hu
  exact (integrand_of_one_le hu.1.le).symm

lemma potential_large {x : ℝ} (hx : 1 ≤ x) :
    potential x = 5 / 3 - x⁻¹ := by
  have hsum := intervalIntegral.integral_add_adjacent_intervals
    (small_integrable (show (0 : ℝ) ≤ 1 by norm_num) le_rfl) (large_integrable hx)
  have hint : (∫ u in (1 : ℝ)..x, weight u / u) = 1 - x⁻¹ := by
    calc
      _ = ∫ u in (1 : ℝ)..x, u ^ (-2 : ℝ) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [Set.uIcc_of_le hx] at hu
        exact integrand_of_one_le hu.1
      _ = _ := by
        rw [integral_rpow (Or.inr ⟨by norm_num, ?_⟩)]
        · norm_num [Real.rpow_neg_one]
          ring
        · rw [Set.uIcc_of_le hx]
          simp
  change potential 1 + _ = potential x at hsum
  rw [potential_small (by norm_num) le_rfl, hint] at hsum
  norm_num [exponent] at hsum
  linarith

lemma fourth_rpow_exponent {u : ℝ} (hu : 0 ≤ u) :
    (u ^ 4) ^ exponent = u ^ 6 := by
  rw [← Real.rpow_natCast_mul hu]
  norm_num [exponent, Real.rpow_natCast]

private lemma weight_fourth {u : ℝ} (hu : 0 ≤ u) :
    weight (u ^ 4) = rootWeight u ^ 2 := by
  by_cases h : u ≤ 1
  · rw [weight_of_le_one (by positivity) (pow_le_one₀ hu h), fourth_rpow_exponent hu]
    simp only [rootWeight, ite_eq_left h]
    ring
  · rw [weight_of_one_le (one_le_pow₀ (le_of_not_ge h))]
    simp only [rootWeight, ite_eq_right h, inv_pow]
    ring

private lemma root_endpoint {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    ((rootWeight u) ^ 2 + (rootWeight v) ^ 2 -
      2 * rootWeight u * rootWeight v * (v / u) ^ 3) * (2 / 3) ≤
        potential (u ^ 4) - potential (v ^ 4) := by
  have up : 0 < u ^ 4 := by positivity
  have vp : 0 < v ^ 4 := by positivity
  by_cases hu1 : u ≤ 1 <;> by_cases hv1 : v ≤ 1
  · rw [potential_small up.le (pow_le_one₀ hu.le hu1),
      potential_small vp.le (pow_le_one₀ hv.le hv1),
      fourth_rpow_exponent hu.le, fourth_rpow_exponent hv.le]
    simp only [rootWeight, ite_eq_left hu1, ite_eq_left hv1, exponent]
    apply le_of_eq
    field_simp
    ring
  · rw [potential_small up.le (pow_le_one₀ hu.le hu1),
      fourth_rpow_exponent hu.le,
      potential_large (one_le_pow₀ (le_of_not_ge hv1))]
    simp only [rootWeight, ite_eq_left hu1, ite_eq_right hv1, exponent]
    have hn : 0 ≤ (v - 1) ^ 2 * (4 * v ^ 3 + 3 * v ^ 2 + 2 * v + 1) := by positivity
    have hid : u ^ 6 / (3 / 2) - (5 / 3 - (v ^ 4)⁻¹) -
        ((u ^ 3) ^ 2 + (v ^ 2)⁻¹ ^ 2 - 2 * u ^ 3 * (v ^ 2)⁻¹ * (v / u) ^ 3) * (2 / 3) =
        ((v - 1) ^ 2 * (4 * v ^ 3 + 3 * v ^ 2 + 2 * v + 1)) / (3 * v ^ 4) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))
  · rw [potential_large (one_le_pow₀ (le_of_not_ge hu1)),
      potential_small vp.le (pow_le_one₀ hv.le hv1), fourth_rpow_exponent hv.le]
    simp only [rootWeight, ite_eq_right hu1, ite_eq_left hv1, exponent]
    have hu5 : 1 ≤ u ^ 5 := one_le_pow₀ (le_of_not_ge hu1)
    have hv6 : v ^ 6 ≤ 1 := pow_le_one₀ hv.le hv1
    have hn : 0 ≤ (u - 1) ^ 2 * (u ^ 3 + 2 * u ^ 2 + 3 * u + 4) +
        4 * (1 - v ^ 6) * (u ^ 5 - 1) := by positivity
    have hid : (5 / 3 - (u ^ 4)⁻¹) - v ^ 6 / (3 / 2) -
        ((u ^ 2)⁻¹ ^ 2 + (v ^ 3) ^ 2 - 2 * (u ^ 2)⁻¹ * v ^ 3 * (v / u) ^ 3) * (2 / 3) =
        ((u - 1) ^ 2 * (u ^ 3 + 2 * u ^ 2 + 3 * u + 4) +
          4 * (1 - v ^ 6) * (u ^ 5 - 1)) / (3 * u ^ 5) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))
  · rw [potential_large (one_le_pow₀ (le_of_not_ge hu1)),
      potential_large (one_le_pow₀ (le_of_not_ge hv1))]
    simp only [rootWeight, ite_eq_right hu1, ite_eq_right hv1]
    have hn : 0 ≤ (u - v) ^ 2 * (u ^ 3 + 2 * u ^ 2 * v + 3 * u * v ^ 2 + 4 * v ^ 3) := by
      positivity
    have hid : (5 / 3 - (u ^ 4)⁻¹) - (5 / 3 - (v ^ 4)⁻¹) -
        ((u ^ 2)⁻¹ ^ 2 + (v ^ 2)⁻¹ ^ 2 - 2 * (u ^ 2)⁻¹ * (v ^ 2)⁻¹ * (v / u) ^ 3) * (2 / 3) =
        ((u - v) ^ 2 * (u ^ 3 + 2 * u ^ 2 * v + 3 * u * v ^ 2 + 4 * v ^ 3)) /
          (3 * u ^ 5 * v ^ 4) := by
      field_simp
      ring
    exact sub_nonneg.mp (hid ▸ div_nonneg hn (by positivity))

private lemma root_remainder {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (weight (u ^ 4) + weight (v ^ 4)) / 6 *
        (v / u - 1) ^ 2 * (3 * (v / u) ^ 2 + 2 * (v / u) + 1) ≤
      scalarRemainder (u ^ 4) (v ^ 4) := by
  have he := root_endpoint hu hv
  have hq : 0 ≤ (rootWeight u - rootWeight v) ^ 2 * (v / u) ^ 3 * (2 / 3) := by
    positivity
  dsimp only [scalarRemainder]
  rw [weight_fourth hu.le, weight_fourth hv.le, ← div_pow]
  nlinarith only [he, hq]

private lemma fourth_ratio_polynomial {t : ℝ} (ht : 0 ≤ t) :
    (t ^ 4 - 1) ^ 2 ≤ 4 * (t - 1) ^ 2 * (3 * t ^ 2 + 2 * t + 1) * (1 + t ^ 4) := by
  have h : 0 ≤ (t - 1) ^ 2 *
      (11 * t ^ 6 + 6 * t ^ 5 + t ^ 2 * (t - 2) ^ 2 + 5 * t ^ 2 + 6 * t + 3) := by
    positivity
  nlinarith only [h]

lemma weight_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ weight x := by
  exact le_min (Real.rpow_nonneg hx _) (inv_nonneg.mpr hx)

private lemma root_remainder_quadratic {u v : ℝ} (hu : 0 < u) (hv : 0 < v) :
    (weight (u ^ 4) + weight (v ^ 4)) * (u ^ 4 - v ^ 4) ^ 2 /
        (24 * u ^ 4 * (u ^ 4 + v ^ 4)) ≤ scalarRemainder (u ^ 4) (v ^ 4) := by
  let w := weight (u ^ 4) + weight (v ^ 4)
  have hw : 0 ≤ w := add_nonneg (weight_nonneg (by positivity)) (weight_nonneg (by positivity))
  calc
    _ = w * ((v / u) ^ 4 - 1) ^ 2 / (24 * (1 + (v / u) ^ 4)) := by
      dsimp only [w]
      field_simp
      ring
    _ ≤ w / 6 * (v / u - 1) ^ 2 * (3 * (v / u) ^ 2 + 2 * (v / u) + 1) := by
      apply (div_le_iff₀ (by positivity : 0 < 24 * (1 + (v / u) ^ 4))).mpr
      have h := mul_le_mul_of_nonneg_left (fourth_ratio_polynomial (by positivity : 0 ≤ v / u)) hw
      nlinarith only [h]
    _ ≤ _ := root_remainder hu hv

lemma scalar_remainder_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) ≤
      scalarRemainder x y := by
  let u := x ^ (1 / 4 : ℝ)
  let v := y ^ (1 / 4 : ℝ)
  have hu : 0 < u := Real.rpow_pos_of_pos hx _
  have hv : 0 < v := Real.rpow_pos_of_pos hy _
  have hux : u ^ 4 = x := by
    simpa only [u, one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) hx.le (by norm_num)
  have hvy : v ^ 4 = y := by
    simpa only [v, one_div, Nat.cast_ofNat] using Real.rpow_inv_natCast_pow (n := 4) hy.le (by norm_num)
  simpa only [hux, hvy] using root_remainder_quadratic hu hv

lemma scalar_remainder_nonneg {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 ≤ scalarRemainder x y := by
  have hwx := weight_nonneg hx.le
  have hwy := weight_nonneg hy.le
  exact (by positivity : 0 ≤ (weight x + weight y) * (x - y) ^ 2 /
    (24 * x * (x + y))).trans (scalar_remainder_lower hx hy)

lemma scalar_remainder_reverse_lower {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) ≤
      (y / x) * scalarRemainder y x := by
  calc
    _ = (y / x) * ((weight y + weight x) * (y - x) ^ 2 / (24 * y * (y + x))) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (scalar_remainder_lower hy hx) (by positivity)

lemma cutoff_nonneg (x : ℝ) : 0 ≤ cutoff x := by
  unfold cutoff
  split_ifs <;> linarith

lemma cutoff_le_one (x : ℝ) : cutoff x ≤ 1 := by
  unfold cutoff
  split_ifs <;> linarith

lemma cutoff_dist_le_one (x y : ℝ) : |cutoff x - cutoff y| ≤ 1 := by
  have hx := cutoff_nonneg x
  have hy := cutoff_nonneg y
  have hx1 := cutoff_le_one x
  have hy1 := cutoff_le_one y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private lemma cutoff_dist_of_le {x y : ℝ} (hxy : x ≤ y) :
    |cutoff x - cutoff y| ≤ 2 * (y - x) := by
  apply abs_le.mpr
  unfold cutoff
  split_ifs <;> constructor <;> linarith

lemma cutoff_dist (x y : ℝ) : |cutoff x - cutoff y| ≤ 2 * |x - y| := by
  rcases le_total x y with h | h
  · rw [abs_of_nonpos (sub_nonpos.mpr h), neg_sub]
    exact cutoff_dist_of_le h
  · rw [abs_sub_comm (cutoff x), abs_of_nonneg (sub_nonneg.mpr h)]
    exact cutoff_dist_of_le h

lemma cutoff_zero_of_not_band {x : ℝ} (h : ¬ (1 / 2 ≤ x ∧ x ≤ 4)) : cutoff x = 0 := by
  unfold cutoff
  split_ifs <;> first | rfl | (exfalso; apply h; constructor <;> linarith)

lemma cutoff_ne_band {x y : ℝ} (h : cutoff x ≠ cutoff y) :
    (1 / 2 ≤ x ∧ x ≤ 4) ∨ (1 / 2 ≤ y ∧ y ≤ 4) := by
  by_contra hn
  have hn := not_or.mp hn
  exact h (by rw [cutoff_zero_of_not_band hn.1, cutoff_zero_of_not_band hn.2])

lemma weight_band {x : ℝ} (hx : 1 / 2 ≤ x ∧ x ≤ 4) : 1 / 4 ≤ weight x := by
  apply le_min
  · calc
      1 / 4 = (1 / 2 : ℝ) ^ (2 : ℝ) := by norm_num
      _ ≤ (1 / 2 : ℝ) ^ exponent :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by norm_num [exponent])
      _ ≤ x ^ exponent := Real.rpow_le_rpow (by norm_num) hx.1 exponent_pos.le
  · simpa only [one_div] using one_div_le_one_div_of_le (by linarith : 0 < x) hx.2

private lemma cutoff_weighted_distance {x y : ℝ} (hx : 0 < x) (hy : 0 < y)
    (hb : x ≤ 4 ∨ y ≤ 4) :
    (1 + y) * (cutoff x - cutoff y) ^ 2 * x * (x + y) ≤ 1200 * (x - y) ^ 2 := by
  let z := |x - y|
  have hz : 0 ≤ z := abs_nonneg _
  have hzx : x ≤ y + z := by have := le_abs_self (x - y); dsimp only [z]; linarith
  have hzy : y ≤ x + z := by have := neg_le_abs (x - y); dsimp only [z]; linarith
  have hsqz : z ^ 2 = (x - y) ^ 2 := sq_abs _
  have hd : (cutoff x - cutoff y) ^ 2 ≤ 4 * z ^ 2 := by
    have h := (sq_le_sq₀ (abs_nonneg (cutoff x - cutoff y)) (by positivity : 0 ≤ 2 * z)).mpr
      (cutoff_dist x y)
    simpa only [sq_abs, mul_pow, show (2 : ℝ) ^ 2 = 4 by norm_num] using h
  have hd1 : (cutoff x - cutoff y) ^ 2 ≤ 1 := by
    have h := (sq_le_sq₀ (abs_nonneg (cutoff x - cutoff y)) (by norm_num : (0 : ℝ) ≤ 1)).mpr
      (cutoff_dist_le_one x y)
    simpa only [sq_abs, one_pow] using h
  have ha : 0 ≤ (1 + y) * x * (x + y) := by positivity
  by_cases hz1 : z ≤ 1
  · have hx5 : x ≤ 5 := by rcases hb with h | h <;> linarith
    have hy5 : y ≤ 5 := by rcases hb with h | h <;> linarith
    have ha300 : (1 + y) * x * (x + y) ≤ 300 := by
      calc
        _ ≤ (6 * 5) * 10 := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 6) hx5 hx.le (by norm_num))
          (by linarith) (by positivity) (by norm_num)
        _ = _ := by norm_num
    have h := mul_le_mul ha300 hd (sq_nonneg _) (by norm_num : (0 : ℝ) ≤ 300)
    nlinarith only [h, hsqz]
  · have hz1 : 1 ≤ z := le_of_not_ge hz1
    have ha1200 : (1 + y) * x * (x + y) ≤ 1200 * z ^ 2 := by
      rcases hb with hb | hb
      · have hy5 : y ≤ 5 * z := by linarith
        have h := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 6 * z) hb hx.le (by positivity))
          (by linarith : x + y ≤ 9 * z) (by positivity) (by positivity : 0 ≤ 6 * z * 4)
        nlinarith only [h, sq_nonneg z]
      · have hx5 : x ≤ 5 * z := by linarith
        have h := mul_le_mul
          (mul_le_mul (by linarith : 1 + y ≤ 5) hx5 hx.le (by norm_num))
          (by linarith : x + y ≤ 9 * z) (by positivity) (by positivity : 0 ≤ 5 * (5 * z))
        nlinarith only [h, sq_nonneg z]
    have h := mul_le_mul ha1200 hd1 (sq_nonneg _) (by positivity : 0 ≤ 1200 * z ^ 2)
    nlinarith only [h, hsqz]

lemma scalar_comparison {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤ scalarRemainder x y ∧
    (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤ (y / x) * scalarRemainder y x := by
  by_cases hf : cutoff x = cutoff y
  · simp only [hf, sub_self, abs_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact ⟨scalar_remainder_nonneg hx hy,
      mul_nonneg (by positivity) (scalar_remainder_nonneg hy hx)⟩
  have hb := cutoff_ne_band hf
  have hw : 1 / 4 ≤ weight x + weight y := by
    have hwx := weight_nonneg hx.le
    have hwy := weight_nonneg hy.le
    rcases hb with hb | hb
    · have := weight_band hb
      linarith
    · have := weight_band hb
      linarith
  have hd := cutoff_weighted_distance hx hy (hb.imp And.right And.right)
  have ht : (1 / 115200) * (1 + y) * |cutoff x - cutoff y| ^ 2 ≤
      (weight x + weight y) * (x - y) ^ 2 / (24 * x * (x + y)) := by
    apply (le_div_iff₀ (by positivity : 0 < 24 * x * (x + y))).mpr
    rw [sq_abs]
    have h := mul_le_mul_of_nonneg_right hw (sq_nonneg (x - y))
    nlinarith only [hd, h]
  exact ⟨ht.trans (scalar_remainder_lower hx hy), ht.trans (scalar_remainder_reverse_lower hx hy)⟩

lemma cutoff_square_le_weight {x : ℝ} (hx : 0 < x) : cutoff x ^ 2 ≤ 4 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  nlinarith

lemma cutoff_weighted_square_le_weight {x : ℝ} (hx : 0 < x) :
    (1 + x) * cutoff x ^ 2 ≤ 20 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  have hf2 : cutoff x ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hf2 (by positivity : 0 ≤ 1 + x)
  nlinarith

lemma cutoff_scaled_square_le_weight {x : ℝ} (hx : 0 < x) :
    x * cutoff x ^ 2 ≤ 16 * weight x := by
  by_cases h : cutoff x = 0
  · rw [h, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
    exact mul_nonneg (by norm_num) (weight_nonneg hx.le)
  have hb : 1 / 2 ≤ x ∧ x ≤ 4 := by
    by_contra hn
    exact h (cutoff_zero_of_not_band hn)
  have hw := weight_band hb
  have hf0 := cutoff_nonneg x
  have hf1 := cutoff_le_one x
  have hf2 : cutoff x ^ 2 ≤ 1 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hf2 hx.le
  nlinarith

end Scalar

section SpectralEndpoints

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

private lemma sum_row (m : ι → κ → ℝ) (f : ι → ℝ) :
    (∑ i, ∑ j, m i j * f i) = ∑ i, (∑ j, m i j) * f i := by
  simp_rw [Finset.sum_mul]

private lemma sum_col (m : ι → κ → ℝ) (f : κ → ℝ) :
    (∑ i, ∑ j, m i j * f j) = ∑ j, (∑ i, m i j) * f j := by
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_mul]

lemma contraction_deficit_identity
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, n i j = 1) (hcol : ∀ j, ∑ i, n i j = 1) :
    (∑ j, potential (y j)) - (∑ i, potential (x i)) =
      (∑ i, ∑ j, n i j * scalarRemainder (y j) (x i)) +
      (∑ i, (1 - ∑ j, m i j) * weight (x i)) / 2 +
      (∑ j, (1 - ∑ i, m i j) * weight (y j)) / 2 := by
  have hp (i : ι) (j : κ) :
      n i j * scalarRemainder (y j) (x i) =
        n i j * potential (y j) - n i j * potential (x i) +
        (m i j * weight (x i) - n i j * weight (x i)) / 2 +
        (m i j * weight (y j) - n i j * weight (y j)) / 2 := by
    rw [hn]
    dsimp only [scalarRemainder]
    field_simp [ne_of_gt (hx i), ne_of_gt (hy j)]
    ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_col n, sum_row n, sum_row m, sum_row n, sum_col m, sum_col n]
  simp_rw [hrow, hcol, one_mul, sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

lemma contraction_spectral_bound
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hm : ∀ i j, 0 ≤ m i j)
    (hmrow : ∀ i, ∑ j, m i j ≤ 1) (hmcol : ∀ j, ∑ i, m i j ≤ 1)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, n i j = 1) (hcol : ∀ j, ∑ i, n i j = 1) :
    (∑ i, ∑ j, m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2) +
      (∑ i, (1 - ∑ j, m i j) * cutoff (x i) ^ 2) +
      (∑ j, (1 - ∑ i, m i j) * (1 + y j) * cutoff (y j) ^ 2) ≤
        115200 * ((∑ j, potential (y j)) - (∑ i, potential (x i))) := by
  have hp (i : ι) (j : κ) :
      m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2 ≤
        115200 * (n i j * scalarRemainder (y j) (x i)) := by
    have h := mul_le_mul_of_nonneg_left (scalar_comparison (hx i) (hy j)).2 (hm i j)
    rw [sq_abs] at h
    rw [hn]
    simp only [div_eq_mul_inv] at h ⊢
    nlinarith only [h]
  have hd (i : ι) : (1 - ∑ j, m i j) * cutoff (x i) ^ 2 ≤
      57600 * ((1 - ∑ j, m i j) * weight (x i)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_square_le_weight (hx i))
      (sub_nonneg.mpr (hmrow i))
    have hnn := mul_nonneg (sub_nonneg.mpr (hmrow i)) (weight_nonneg (hx i).le)
    nlinarith only [h, hnn]
  have he (j : κ) : (1 - ∑ i, m i j) * (1 + y j) * cutoff (y j) ^ 2 ≤
      57600 * ((1 - ∑ i, m i j) * weight (y j)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_weighted_square_le_weight (hy j))
      (sub_nonneg.mpr (hmcol j))
    have hnn := mul_nonneg (sub_nonneg.mpr (hmcol j)) (weight_nonneg (hy j).le)
    nlinarith only [h, hnn]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  have he := Finset.sum_le_sum (s := Finset.univ) (fun j _ => he j)
  simp_rw [← Finset.mul_sum] at hs hd he
  rw [contraction_deficit_identity x y m n hx hy hn hrow hcol]
  linarith only [hs, hd, he]

lemma gain_deficit_identity
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hrow : ∀ i, ∑ j, m i j = 1) (hcol : ∀ j, ∑ i, m i j = 1) :
    (∑ i, potential (x i)) - (∑ j, potential (y j)) =
      (∑ i, ∑ j, m i j * scalarRemainder (x i) (y j)) +
      (∑ i, (1 - ∑ j, n i j) * weight (x i)) / 2 +
      (∑ j, (1 - ∑ i, n i j) * weight (y j)) / 2 := by
  have hp (i : ι) (j : κ) :
      m i j * scalarRemainder (x i) (y j) =
        m i j * potential (x i) - m i j * potential (y j) +
        (n i j * weight (x i) - m i j * weight (x i)) / 2 +
        (n i j * weight (y j) - m i j * weight (y j)) / 2 := by
    rw [hn]
    dsimp only [scalarRemainder]
    field_simp [ne_of_gt (hx i)]
    ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib]
  rw [sum_row m, sum_col m, sum_row n, sum_row m, sum_col n, sum_col m]
  simp_rw [hrow, hcol, one_mul, sub_mul, one_mul, Finset.sum_sub_distrib]
  ring

lemma gain_spectral_bound
    (x : ι → ℝ) (y : κ → ℝ) (m n : ι → κ → ℝ)
    (hx : ∀ i, 0 < x i) (hy : ∀ j, 0 < y j)
    (hm : ∀ i j, 0 ≤ m i j)
    (hrow : ∀ i, ∑ j, m i j = 1) (hcol : ∀ j, ∑ i, m i j = 1)
    (hn : ∀ i j, n i j = m i j * y j / x i)
    (hnrow : ∀ i, ∑ j, n i j ≤ 1) (hncol : ∀ j, ∑ i, n i j ≤ 1) :
    (∑ i, ∑ j, m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2) +
      (∑ i, x i * (1 - ∑ j, n i j) * cutoff (x i) ^ 2) ≤
        115200 * ((∑ i, potential (x i)) - (∑ j, potential (y j))) := by
  have hp (i : ι) (j : κ) :
      m i j * (1 + y j) * (cutoff (x i) - cutoff (y j)) ^ 2 ≤
        115200 * (m i j * scalarRemainder (x i) (y j)) := by
    have h := mul_le_mul_of_nonneg_left (scalar_comparison (hx i) (hy j)).1 (hm i j)
    rw [sq_abs] at h
    nlinarith only [h]
  have hd (i : ι) : x i * (1 - ∑ j, n i j) * cutoff (x i) ^ 2 ≤
      57600 * ((1 - ∑ j, n i j) * weight (x i)) := by
    have h := mul_le_mul_of_nonneg_left (cutoff_scaled_square_le_weight (hx i))
      (sub_nonneg.mpr (hnrow i))
    have hnn := mul_nonneg (sub_nonneg.mpr (hnrow i)) (weight_nonneg (hx i).le)
    nlinarith only [h, hnn]
  have he : 0 ≤ ∑ j, (1 - ∑ i, n i j) * weight (y j) :=
    Finset.sum_nonneg (fun j _ =>
      mul_nonneg (sub_nonneg.mpr (hncol j)) (weight_nonneg (hy j).le))
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun j _ => hp i j))
  have hd := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hd i)
  simp_rw [← Finset.mul_sum] at hs hd
  rw [gain_deficit_identity x y m n hx hn hrow hcol]
  linarith only [hs, hd, he]

end SpectralEndpoints

section RealMatrices

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma hermitian_dot (A : Matrix ι ι ℝ) (hA : A.IsHermitian)
    (x y : ι → ℝ) : x ⬝ᵥ (A *ᵥ y) = (A *ᵥ x) ⬝ᵥ y := by
  have ht : A.transpose = A := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hA
  have hx : x ᵥ* A = A *ᵥ x := by simpa only [ht] using Matrix.vecMul_transpose A x
  rw [Matrix.dotProduct_mulVec, hx]

lemma le_of_square_le {S T : Matrix ι ι ℝ} (hS : S.PosSemidef)
    (hT : T.PosSemidef) (hst : S * S ≤ T * T) : S ≤ T := by
  let D := T - S
  have hD : D.IsHermitian := hT.1.sub hS.1
  change D.PosSemidef
  apply hD.posSemidef_iff_eigenvalues_nonneg.mpr
  intro i
  let v : ι → ℝ := (hD.eigenvectorBasis i).ofLp
  let eig := hD.eigenvalues i
  have heig : D *ᵥ v = eig • v := hD.mulVec_eigenvectorBasis i
  have hv : v ⬝ᵥ v = 1 := by
    have hn := real_inner_self_eq_norm_sq (hD.eigenvectorBasis i)
    simpa only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial,
      OrthonormalBasis.norm_eq_one, one_pow] using hn
  have hs : 0 ≤ v ⬝ᵥ (S *ᵥ v) := by
    simpa only [star_trivial] using hS.dotProduct_mulVec_nonneg v
  have ht : 0 ≤ v ⬝ᵥ (T *ᵥ v) := by
    simpa only [star_trivial] using hT.dotProduct_mulVec_nonneg v
  have hd : v ⬝ᵥ (T *ᵥ v) - v ⬝ᵥ (S *ᵥ v) = eig := by
    have hdv : v ⬝ᵥ (D *ᵥ v) = eig := by rw [heig, dotProduct_smul, hv]; simp
    simpa only [D, Matrix.sub_mulVec, dotProduct_sub] using hdv
  have hq : 0 ≤ v ⬝ᵥ ((T * T - S * S) *ᵥ v) := by
    simpa only [star_trivial] using (Matrix.le_iff.mp hst).dotProduct_mulVec_nonneg v
  have hid : T * T - S * S = T * D + D * S := by dsimp [D]; noncomm_ring
  have hformula : v ⬝ᵥ ((T * T - S * S) *ᵥ v) =
      eig * (v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v)) := by
    rw [hid, Matrix.add_mulVec, dotProduct_add, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, dotProduct_smul,
      hermitian_dot D hD, heig, smul_dotProduct]
    simp only [smul_eq_mul]
    ring
  rw [hformula] at hq
  change 0 ≤ eig
  by_contra hh
  have hn : eig < 0 := lt_of_not_ge hh
  have hp : 0 < v ⬝ᵥ (T *ᵥ v) + v ⬝ᵥ (S *ᵥ v) := by linarith
  exact (not_lt_of_ge hq) (mul_neg_of_neg_of_pos hn hp)

lemma sqrt_le_sqrt {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) (hab : A ≤ B) : CFC.sqrt A ≤ CFC.sqrt B := by
  apply le_of_square_le (CFC.sqrt_nonneg A).posSemidef (CFC.sqrt_nonneg B).posSemidef
  simpa only [← sq, CFC.sq_sqrt A hA.nonneg, CFC.sq_sqrt B hB.nonneg] using hab

lemma inv_le_inv {A B : Matrix ι ι ℝ} (hA : A.PosDef) (hB : B.PosDef)
    (hab : A ≤ B) : B⁻¹ ≤ A⁻¹ := by
  let _ := hA.isUnit.invertible
  let _ := hB.isUnit.invertible
  have hD : (A⁻¹ - B⁻¹).IsHermitian := hA.1.inv.sub hB.1.inv
  have h₁ := hA.posSemidef.conjTranspose_mul_mul_same (A⁻¹ - B⁻¹)
  rw [hD.eq] at h₁
  have h₂ := (Matrix.le_iff.mp hab).conjTranspose_mul_mul_same B⁻¹
  rw [hB.1.inv.eq] at h₂
  have hid : (A⁻¹ - B⁻¹) * A * (A⁻¹ - B⁻¹) + B⁻¹ * (B - A) * B⁻¹ =
      A⁻¹ - B⁻¹ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.inv_mul_of_invertible,
      Matrix.mul_one, Matrix.one_mul]
    abel
  exact Matrix.le_iff.mpr (hid ▸ h₁.add h₂)

lemma trace_mul_nonneg {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have h := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  rw [hS.eq] at h
  have ht := h.trace_nonneg
  rw [Matrix.trace_mul_cycle, ← sq, CFC.sq_sqrt A hA.nonneg] at ht
  exact ht

lemma trace_mul_mono_right {A B Q : Matrix ι ι ℝ}
    (hab : A ≤ B) (hQ : Q.PosSemidef) : (A * Q).trace ≤ (B * Q).trace := by
  have h := trace_mul_nonneg (Matrix.le_iff.mp hab) hQ
  simpa only [Matrix.sub_mul, Matrix.trace_sub, sub_nonneg] using h

end RealMatrices
end EuclideanSteinitz.MatrixEnergy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Spectral
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Real spectral calculus and noncommuting matrix inequalities. -/

namespace EuclideanSteinitz.Spectral
open Matrix
open scoped MatrixOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_transpose_mul (U : unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ).transpose * U = 1 := by
  simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
    Unitary.coe_star_mul_self U

lemma unitary_mul_transpose (U : unitaryGroup ι ℝ) :
    (U : Matrix ι ι ℝ) * (U : Matrix ι ι ℝ).transpose = 1 := by
  simpa only [Unitary.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial] using Unitary.coe_mul_star_self U

lemma real_spectral {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hA.eigenvalues *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  simpa only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq, Function.comp_def]
    using hA.spectral_theorem

lemma real_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) *
      diagonal (fun i => f (hA.eigenvalues i)) *
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc]
  simp only [Unitary.conjStarAlgAut_apply, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial, RCLike.ofReal_real_eq_id, id_eq, Function.comp_def]

lemma trace_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [real_cfc hA f, trace_mul_cycle, unitary_transpose_mul, one_mul, trace_diagonal]

lemma trace_spectral {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    A.trace = ∑ i, hA.eigenvalues i := by
  conv_lhs => rw [real_spectral hA]
  rw [trace_mul_cycle, unitary_transpose_mul, one_mul, trace_diagonal]

lemma trace_transpose_conjugate (U : unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    ((U : Matrix ι ι ℝ).transpose * A * U).trace = A.trace := by
  rw [trace_mul_cycle, unitary_mul_transpose, one_mul]

lemma sum_row_squares (U : unitaryGroup ι ℝ) (i : ι) :
    ∑ j, (U i j) ^ 2 = 1 := by
  have h := congr_fun (congr_fun (unitary_mul_transpose U) i) i
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq, sq] using h

lemma sum_col_squares (U : unitaryGroup ι ℝ) (j : ι) :
    ∑ i, (U i j) ^ 2 = 1 := by
  have h := congr_fun (congr_fun (unitary_transpose_mul U) j) j
  simpa only [Matrix.mul_apply, transpose_apply, Matrix.one_apply_eq, sq] using h

lemma overlapBasis_coe {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (overlapBasis hA hB : Matrix ι ι ℝ) =
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * hB.eigenvectorUnitary := by
  simp only [overlapBasis, Submonoid.coe_mul, Unitary.coe_star, star_eq_conjTranspose,
    conjTranspose_eq_transpose_of_trivial]

lemma cfc_mixed_basis {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (cfc f A - cfc g B) *
        hB.eigenvectorUnitary =
      diagonal (fun i => f (hA.eigenvalues i)) * overlapBasis hA hB -
        (overlapBasis hA hB : Matrix ι ι ℝ) * diagonal (fun j => g (hB.eigenvalues j)) := by
  rw [Matrix.mul_sub, Matrix.sub_mul, real_cfc hA f, real_cfc hB g, overlapBasis_coe]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  simp only [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma cfc_mixed_basis_apply {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) (i j : ι) :
    ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (cfc f A - cfc g B) *
        hB.eigenvectorUnitary) i j =
      (f (hA.eigenvalues i) - g (hB.eigenvalues j)) * overlapBasis hA hB i j := by
  rw [cfc_mixed_basis, Matrix.sub_apply, diagonal_mul, mul_diagonal]
  ring

omit [DecidableEq ι] in
lemma trace_sandwich_diagonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (D : Matrix ι κ ℝ) (w : κ → ℝ) :
    (D * diagonal w * D.transpose).trace = ∑ i, ∑ j, w j * (D i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [mul_apply (M := D * diagonal w), mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_weighted_basis {κ : Type*} [Fintype κ] [DecidableEq κ]
    (U : unitaryGroup ι ℝ) (V : unitaryGroup κ ℝ)
    (D : Matrix ι κ ℝ) (w : κ → ℝ) :
    (D * ((V : Matrix κ κ ℝ) * diagonal w * (V : Matrix κ κ ℝ).transpose) *
      D.transpose).trace =
      ∑ i, ∑ j, w j * ((U : Matrix ι ι ℝ).transpose * D * (V : Matrix κ κ ℝ)) i j ^ 2 := by
  rw [← trace_sandwich_diagonal, Matrix.transpose_mul, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  rw [← trace_transpose_conjugate U
    (D * ((V : Matrix κ κ ℝ) * diagonal w * (V : Matrix κ κ ℝ).transpose) *
      D.transpose)]
  simp only [Matrix.mul_assoc]

lemma weighted_cfc_distance {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g w : ℝ → ℝ) :
    ((cfc f A - cfc g B) * cfc w B * (cfc f A - cfc g B).transpose).trace =
      ∑ i, ∑ j, (overlapBasis hA hB i j) ^ 2 * w (hB.eigenvalues j) *
        (f (hA.eigenvalues i) - g (hB.eigenvalues j)) ^ 2 := by
  rw [real_cfc hB w, trace_weighted_basis hA.eigenvectorUnitary hB.eigenvectorUnitary]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [cfc_mixed_basis_apply]
  ring

lemma trace_diagonal_product (M : Matrix ι ι ℝ) (a b : ι → ℝ) :
    (diagonal a * M * diagonal b * M.transpose).trace =
      ∑ i, ∑ j, a i * b j * (M i j) ^ 2 := by
  simp only [Matrix.trace, Matrix.diag]
  simp_rw [mul_apply (M := diagonal a * M * diagonal b), mul_diagonal,
    diagonal_mul, transpose_apply]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma trace_cfc_product {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f g : ℝ → ℝ) :
    (cfc f A * cfc g B).trace = ∑ i, ∑ j,
      (overlapBasis hA hB i j) ^ 2 * f (hA.eigenvalues i) * g (hB.eigenvalues j) := by
  rw [real_cfc hA f, real_cfc hB g]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) *
        (overlapBasis hA hB : Matrix ι ι ℝ) *
        diagonal (fun j => g (hB.eigenvalues j)) *
        (overlapBasis hA hB : Matrix ι ι ℝ).transpose).trace := by
      rw [overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
      simp only [Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [trace_diagonal_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

lemma overlap_sum_left (U : unitaryGroup ι ℝ) (f : ι → ℝ) :
    (∑ i, ∑ j, (U i j) ^ 2 * f i) = ∑ i, f i := by
  simp only [← Finset.sum_mul, sum_row_squares, one_mul]

lemma overlap_sum_right (U : unitaryGroup ι ℝ) (g : ι → ℝ) :
    (∑ i, ∑ j, (U i j) ^ 2 * g j) = ∑ j, g j := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, sum_col_squares, one_mul]

lemma trace_cfc_remainder {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f f' : ℝ → ℝ) :
    (cfc f A).trace - (cfc f B).trace - (cfc f' B * (A - B)).trace =
      ∑ i, ∑ j, (overlapBasis hA hB i j) ^ 2 *
        (f (hA.eigenvalues i) - f (hB.eigenvalues j) -
         f' (hB.eigenvalues j) * (hA.eigenvalues i - hB.eigenvalues j)) := by
  have hprod := trace_cfc_product hA hB id f'
  rw [cfc_id ℝ A hA.isSelfAdjoint] at hprod
  rw [Matrix.mul_sub, Matrix.trace_sub,
    Matrix.trace_mul_comm (cfc f' B) A, hprod]
  have hs : (cfc f' B * B).trace = ∑ j, f' (hB.eigenvalues j) * hB.eigenvalues j := by
    calc
      _ = (cfc f' B * cfc (id : ℝ → ℝ) B).trace := by
        rw [cfc_id ℝ B hB.isSelfAdjoint]
      _ = _ := by
        have hf : ContinuousOn f' (spectrum ℝ B) := by
          rw [continuousOn_iff_continuous_domRestrict]
          fun_prop
        rw [← cfc_mul f' id B hf continuousOn_id, trace_cfc hB]
        rfl
  rw [hs, trace_cfc hA, trace_cfc hB]
  conv_lhs =>
    arg 1
    arg 1
    rw [← overlap_sum_left (overlapBasis hA hB) (fun i => f (hA.eigenvalues i))]
  rw [← overlap_sum_right (overlapBasis hA hB) (fun j => f (hB.eigenvalues j)),
    ← overlap_sum_right (overlapBasis hA hB)
      (fun j => f' (hB.eigenvalues j) * hB.eigenvalues j)]
  simp only [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [id_eq]
  ring

omit [Fintype ι] [DecidableEq ι] in
lemma convex_tangent {S : Set ℝ} {f : ℝ → ℝ} {x y d : ℝ}
    (hf : ConvexOn ℝ S f) (hx : x ∈ S) (hy : y ∈ S)
    (hd : HasDerivWithinAt f d S y) : d * (x - y) ≤ f x - f y := by
  rcases lt_trichotomy x y with h | rfl | h
  · have hs := hf.slope_le_of_hasDerivWithinAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr h)] at hs
    nlinarith
  · simp
  · have hs := hf.le_slope_of_hasDerivWithinAt hy hx h hd
    rwa [slope_def_field, le_div_iff₀ (sub_pos.mpr h)] at hs

lemma trace_tangent_le {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (f f' : ℝ → ℝ)
    {S : Set ℝ} (hAS : ∀ i, hA.eigenvalues i ∈ S)
    (hBS : ∀ j, hB.eigenvalues j ∈ S)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y) :
    (cfc f' B * (A - B)).trace ≤ (cfc f A).trace - (cfc f B).trace := by
  apply sub_nonneg.mp
  rw [trace_cfc_remainder hA hB]
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (htan _ (hAS i) _ (hBS j)))

omit [Fintype ι] [DecidableEq ι] in
lemma hasDerivWithinAt_of_tangents {p d : ℝ → ℝ} {T : Set ℝ} {t : ℝ}
    (hd : ContinuousWithinAt d T t)
    (hl : ∀ u ∈ T, d t * (u - t) ≤ p u - p t)
    (hu : ∀ u ∈ T, p u - p t ≤ d u * (u - t)) :
    HasDerivWithinAt p (d t) T t := by
  rw [hasDerivWithinAt_iff_tendsto]
  apply squeeze_zero' (Filter.Eventually.of_forall (fun u => by positivity))
  · filter_upwards [self_mem_nhdsWithin] with u hut
    have hlo := hl u hut
    have hup := hu u hut
    have he : 0 ≤ p u - p t - (u - t) * d t := by linarith
    have he' : p u - p t - (u - t) * d t ≤ (u - t) * (d u - d t) := by nlinarith
    have hnorm : ‖p u - p t - (u - t) • d t‖ ≤ ‖u - t‖ * ‖d u - d t‖ := by
      rw [smul_eq_mul, Real.norm_of_nonneg he, ← norm_mul]
      exact he'.trans (le_abs_self _)
    calc
      _ ≤ ‖u - t‖⁻¹ * (‖u - t‖ * ‖d u - d t‖) :=
        mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr (norm_nonneg _))
      _ ≤ ‖d u - d t‖ := by
        by_cases h : u = t
        · simp [h]
        · rw [← mul_assoc, inv_mul_cancel₀ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)), one_mul]
  · simpa only [sub_self, norm_zero] using (hd.tendsto.sub (tendsto_const_nhds : Filter.Tendsto
      (fun _ : ℝ => d t) (nhdsWithin t T) (nhds (d t)))).norm

open scoped Matrix.Norms.L2Operator in
lemma trace_cfc_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (f f' : ℝ → ℝ)
    {T S : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hS : ∀ u ∈ T, spectrum ℝ (A + u • H) ⊆ S)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y)
    (hc : ContinuousWithinAt (fun u : ℝ => cfc f' (A + u • H)) T t) :
    HasDerivWithinAt (fun u : ℝ => (cfc f (A + u • H)).trace)
      (cfc f' (A + t • H) * H).trace T t := by
  have herm (u : ℝ) : (A + u • H).IsHermitian :=
    hA.add (hH.smul (IsSelfAdjoint.all u))
  have mem (u : ℝ) (hu : u ∈ T) (i : ι) :
      (herm u).eigenvalues i ∈ S := hS u hu ((herm u).eigenvalues_mem_spectrum_real i)
  have htrace : Continuous (Matrix.trace : Matrix ι ι ℝ → ℝ) :=
    (Matrix.traceLinearMap ι ℝ ℝ).continuous_of_finiteDimensional
  have hc' : ContinuousWithinAt (fun u : ℝ => (cfc f' (A + u • H) * H).trace) T t := by
    exact htrace.continuousAt.comp_continuousWithinAt (hc.mul continuousWithinAt_const)
  apply hasDerivWithinAt_of_tangents hc'
  · intro u hu
    have h := trace_tangent_le (herm u) (herm t) f f' (mem u hu) (mem t ht) htan
    have heq : A + u • H - (A + t • H) = (u - t) • H := by module
    simpa only [heq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul, mul_comm] using h
  · intro u hu
    have h := trace_tangent_le (herm t) (herm u) f f' (mem t ht) (mem u hu) htan
    have heq : A + t • H - (A + u • H) = (t - u) • H := by module
    simp only [heq, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at h
    nlinarith

open scoped Matrix.Norms.L2Operator in
lemma continuous_cfc_affine {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {f : ℝ → ℝ} (hf : Continuous f) :
    Continuous (fun u : ℝ => cfc f (A + u • H)) := by
  apply Continuous.cfc_of_mem_nhdsSet (s := Set.univ) f (by simp)
    (continuous_const.add (continuous_id.smul continuous_const))
    (fun u => (hA.add (hH.smul (IsSelfAdjoint.all u))).isSelfAdjoint) hf.continuousOn

open scoped Matrix.Norms.L2Operator in

lemma trace_rpow_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {a : ℝ} (ha : 1 ≤ a)
    {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hpos : ∀ u ∈ T, (A + u • H).PosSemidef) :
    HasDerivWithinAt (fun u : ℝ => (cfc (fun x : ℝ => x ^ a) (A + u • H)).trace)
      (a * (cfc (fun x : ℝ => x ^ (a - 1)) (A + t • H) * H).trace) T t := by
  have hf' : Continuous (fun x : ℝ => a * x ^ (a - 1)) :=
    continuous_const.mul (Real.continuous_rpow_const (sub_nonneg.mpr ha))
  have hd := trace_cfc_affine_derivative hA hH (fun x : ℝ => x ^ a)
    (fun x : ℝ => a * x ^ (a - 1)) (S := Set.Ici 0) ht
    (fun u hu x hx => spectrum_nonneg_of_nonneg (hpos u hu).nonneg hx)
    (fun x hx y hy => convex_tangent (convexOn_rpow ha) hx hy
      (Real.hasDerivAt_rpow_const (Or.inr ha)).hasDerivWithinAt)
    (continuous_cfc_affine hA hH hf').continuousWithinAt
  simpa only [cfc_const_mul a (fun x : ℝ => x ^ (a - 1)) _
      (Real.continuous_rpow_const (sub_nonneg.mpr ha)).continuousOn,
    Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] using hd

lemma trace_psd_pairing {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  have hS : (CFC.sqrt A).IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have h := hB.conjTranspose_mul_mul_same (CFC.sqrt A)
  rw [hS.eq] at h
  have ht := h.trace_nonneg
  rw [Matrix.trace_mul_cycle, ← sq, CFC.sq_sqrt A hA.nonneg] at ht
  exact ht

lemma trace_convex_monotone {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hAB : A ≤ B)
    (f f' : ℝ → ℝ) {S : Set ℝ}
    (hAS : ∀ i, hA.eigenvalues i ∈ S) (hBS : ∀ i, hB.eigenvalues i ∈ S)
    (hfp : ∀ y ∈ S, 0 ≤ f' y)
    (htan : ∀ x ∈ S, ∀ y ∈ S, f' y * (x - y) ≤ f x - f y) :
    (cfc f A).trace ≤ (cfc f B).trace := by
  have hp : (cfc f' A).PosSemidef := by
    apply Matrix.nonneg_iff_posSemidef.mp
    apply cfc_nonneg
    intro x hx
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    exact hfp _ (hAS i)
  have h := trace_tangent_le hB hA f f' hBS hAS htan
  have h0 := trace_psd_pairing hp (Matrix.le_iff.mp hAB)
  linarith

lemma trace_rpow_monotone {A B : Matrix ι ι ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) (hAB : A ≤ B)
    {a : ℝ} (ha : 1 ≤ a) :
    (cfc (fun x : ℝ => x ^ a) A).trace ≤ (cfc (fun x : ℝ => x ^ a) B).trace := by
  apply trace_convex_monotone hA.1 hB.1 hAB _ (fun x => a * x ^ (a - 1))
    (S := Set.Ici 0) (fun i => hA.eigenvalues_nonneg i) (fun i => hB.eigenvalues_nonneg i)
  · intro y hy
    exact mul_nonneg (by linarith) (Real.rpow_nonneg hy _)
  · intro x hx y hy
    exact convex_tangent (convexOn_rpow ha) hx hy
      (Real.hasDerivAt_rpow_const (Or.inr ha)).hasDerivWithinAt

lemma trace_cfc_eq_of_charpoly {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (h : A.charpoly = B.charpoly)
    (f : ℝ → ℝ) : (cfc f A).trace = (cfc f B).trace := by
  rw [trace_cfc hA, trace_cfc hB, (hA.eigenvalues_eq_eigenvalues_iff hB).mpr h]

lemma transpose_contraction {C : Matrix ι ι ℝ} (hC : C * C.transpose ≤ 1) :
    C.transpose * C ≤ 1 := by
  have h₁ : (C * C.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_conjTranspose_self C
  have h₂ : (C.transpose * C).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self C
  have heq := (h₂.eigenvalues_eq_eigenvalues_iff h₁).mpr (charpoly_mul_comm C.transpose C)
  rw [CFC.le_one_iff (R := ℝ) _ h₂.isSelfAdjoint]
  rw [CFC.le_one_iff (R := ℝ) _ h₁.isSelfAdjoint] at hC
  intro x hx
  rw [h₂.spectrum_real_eq_range_eigenvalues, heq, ← h₁.spectrum_real_eq_range_eigenvalues] at hx
  exact hC x hx

lemma trace_rpow_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) {a : ℝ} (ha : 1 ≤ a) :
    (cfc (fun x : ℝ => x ^ a) (C * A * C.transpose)).trace ≤
      (cfc (fun x : ℝ => x ^ a) A).trace := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [trace_cfc_eq_of_charpoly hCA.1 hSC.1 heq]
  exact trace_rpow_monotone hSC hA hle ha

end EuclideanSteinitz.Spectral

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Gain
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Contraction and gain potentials for positive semidefinite matrices. -/

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma transpose_bound {C : Matrix ι ι ℝ} {r : ℝ}
    (hC : C * C.transpose ≤ r • (1 : Matrix ι ι ℝ)) :
    C.transpose * C ≤ r • (1 : Matrix ι ι ℝ) := by
  have h₁ : (C * C.transpose).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_mul_conjTranspose_self C
  have h₂ : (C.transpose * C).IsHermitian := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using isHermitian_conjTranspose_mul_self C
  have heq := (h₂.eigenvalues_eq_eigenvalues_iff h₁).mpr (charpoly_mul_comm C.transpose C)
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le h₂.isSelfAdjoint]
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le h₁.isSelfAdjoint] at hC
  intro x hx
  rw [h₂.spectrum_real_eq_range_eigenvalues, heq, ← h₁.spectrum_real_eq_range_eigenvalues] at hx
  exact hC x hx

lemma cube_le_eight {K : Matrix ι ι ℝ} (hK : K.PosSemidef)
    (hK₂ : K ≤ (2 : ℝ) • (1 : Matrix ι ι ℝ)) :
    K ^ 3 ≤ (8 : ℝ) • (1 : Matrix ι ι ℝ) := by
  rw [← cfc_pow_id (R := ℝ) K 3 hK.1.isSelfAdjoint, ← Algebra.algebraMap_eq_smul_one,
    ← cfc_const (R := ℝ) (8 : ℝ) K hK.1.isSelfAdjoint,
    cfc_le_iff _ _ _ (by fun_prop) (by fun_prop) hK.1.isSelfAdjoint]
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le hK.1.isSelfAdjoint] at hK₂
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hK.nonneg hx
  have hx₂ := hK₂ x hx
  nlinarith [mul_nonneg hx₀ (sq_nonneg (x - 2)), sq_nonneg (x - 2)]

lemma relative_sqrt_bound {T H A : Matrix ι ι ℝ}
    (hT : IsUnit T) (hH : H.PosSemidef) (hA : A.PosSemidef)
    (hAeq : A = T * H * T.transpose)
    (hTT : T * T.transpose = 1 + A) (hA₁ : A ≤ 1) :
    T.transpose * CFC.sqrt A * T ≤ Real.sqrt 8 • CFC.sqrt H := by
  let K := T.transpose * T
  let B := T.transpose * CFC.sqrt A * T
  let R := CFC.sqrt A
  have hTt : IsUnit T.transpose := (Matrix.isUnit_transpose T).mpr hT
  let _ := hTt.invertible
  have hK : K.PosSemidef := by
    simpa only [K, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
      (star_mul_self_nonneg T : (0 : Matrix ι ι ℝ) ≤ star T * T).posSemidef
  have hKH : K * H = K - 1 := by
    have h := congrArg (fun M : Matrix ι ι ℝ => T.transpose * M * T.transpose⁻¹) hTT
    rw [hAeq] at h
    simp only [Matrix.mul_add, Matrix.mul_one, Matrix.add_mul, Matrix.mul_assoc,
      Matrix.mul_inv_of_invertible, Matrix.mul_one] at h
    change K = 1 + T.transpose * (T * H) at h
    rw [← Matrix.mul_assoc] at h
    exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using h.symm)
  have hHK : H * K = K - 1 := by
    have h := congrArg Matrix.conjTranspose hKH
    simpa only [conjTranspose_mul, conjTranspose_sub, conjTranspose_one,
      hH.1.eq, hK.1.eq] using h
  have hcomm : Commute H K := by exact hHK.trans hKH.symm
  have hK₂ : K ≤ (2 : ℝ) • (1 : Matrix ι ι ℝ) := by
    apply transpose_bound
    rw [hTT, two_smul]
    exact add_le_add le_rfl hA₁
  have hB : B.PosSemidef := by
    simpa only [B, conjTranspose_eq_transpose_of_trivial] using
      (CFC.sqrt_nonneg A).posSemidef.conjTranspose_mul_mul_same T
  have hRR : R * R = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hBB : B * B = H * K ^ 3 := by
    calc
      B * B = T.transpose * (R * (T * T.transpose) * R) * T := by
        dsimp [B, R]; simp only [Matrix.mul_assoc]
      _ = T.transpose * (A * (1 + A)) * T := by
        rw [hTT, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hRR]
        have hr : R * A * R = A * A := by
          rw [← hRR]; simp only [Matrix.mul_assoc]
        rw [hr]
        noncomm_ring
      _ = K * H * K * K := by
        rw [← hTT, hAeq]
        dsimp [K]
        simp only [Matrix.mul_assoc]
      _ = H * K ^ 3 := by rw [hcomm.eq.symm]; noncomm_ring
  have hsq : B * B ≤ (8 : ℝ) • H := by
    have hp := hcomm.pow_right 3
    have hc : Commute H ((8 : ℝ) • (1 : Matrix ι ι ℝ) - K ^ 3) :=
      (Commute.one_right H).smul_right 8 |>.sub_right hp
    have hh := hc.mul_nonneg hH.nonneg (sub_nonneg.mpr (cube_le_eight hK hK₂))
    rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← hBB] at hh
    exact sub_nonneg.mp hh
  have hroot : (Real.sqrt 8 • CFC.sqrt H : Matrix ι ι ℝ).PosSemidef :=
    (smul_nonneg (Real.sqrt_nonneg 8) (CFC.sqrt_nonneg H)).posSemidef
  apply MatrixEnergy.le_of_square_le hB hroot
  simpa only [smul_mul_assoc, mul_smul_comm, smul_smul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 8),
    CFC.sqrt_mul_sqrt_self H hH.nonneg] using hsq

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma inverseSqrt_psd (M : Matrix ι ι ℝ) : (inverseSqrt M).PosSemidef :=
  (CFC.sqrt_nonneg M).posSemidef.inv

lemma inverseSqrt_transpose (M : Matrix ι ι ℝ) : (inverseSqrt M).transpose = inverseSqrt M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (inverseSqrt_psd M).1.eq

lemma sqrt_transpose (M : Matrix ι ι ℝ) : (CFC.sqrt M).transpose = CFC.sqrt M := by
  simpa only [conjTranspose_eq_transpose_of_trivial] using (CFC.sqrt_nonneg M).posSemidef.1.eq

lemma inverseSqrt_mul_sqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * CFC.sqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.inv_mul_of_invertible _

lemma sqrt_mul_inverseSqrt {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    CFC.sqrt M * inverseSqrt M = 1 := by
  have h := (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit
  let _ := h.invertible
  exact Matrix.mul_inv_of_invertible _

lemma inverseSqrt_sandwich {M : Matrix ι ι ℝ} (hM : M.PosDef) :
    inverseSqrt M * M * inverseSqrt M = 1 := by
  calc
    _ = inverseSqrt M * (CFC.sqrt M * CFC.sqrt M) * inverseSqrt M := by
      rw [CFC.sqrt_mul_sqrt_self M hM.posSemidef.nonneg]
    _ = 1 := by rw [← Matrix.mul_assoc, inverseSqrt_mul_sqrt hM, Matrix.one_mul,
      sqrt_mul_inverseSqrt hM]

lemma inverseSqrt_unit {M : Matrix ι ι ℝ} (hM : M.PosDef) : IsUnit (inverseSqrt M) := by
  rw [inverseSqrt, nonsing_inv_eq_ringInverse, isUnit_ringInverse]
  exact (CFC.isUnit_sqrt_iff M hM.posSemidef.nonneg).mpr hM.isUnit

omit [DecidableEq ι] in
lemma congruence_mono {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (L : Matrix ι ι ℝ) :
    L * A * L.transpose ≤ L * B * L.transpose := by
  apply Matrix.le_iff.mpr
  simpa only [Matrix.mul_sub, Matrix.sub_mul, conjTranspose_eq_transpose_of_trivial]
    using (Matrix.le_iff.mp hAB).mul_mul_conjTranspose_same L

lemma trace_power_bound {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {a q : ℝ}
    (ha : 0 < a) (hq : 0 ≤ q) (htr : (cfc (fun x : ℝ => x ^ a) A).trace ≤ q ^ a) :
    A ≤ q • (1 : Matrix ι ι ℝ) := by
  rw [← Algebra.algebraMap_eq_smul_one, le_algebraMap_iff_spectrum_le hA.1.isSelfAdjoint]
  rw [Spectral.trace_cfc hA.1] at htr
  intro x hx
  rw [hA.1.spectrum_real_eq_range_eigenvalues] at hx
  obtain ⟨i, rfl⟩ := hx
  have hs := Finset.single_le_sum (s := Finset.univ)
    (f := fun j => hA.1.eigenvalues j ^ a)
    (fun j _ => Real.rpow_nonneg (hA.eigenvalues_nonneg j) a) (Finset.mem_univ i)
  exact (Real.rpow_le_rpow_iff (hA.eigenvalues_nonneg i) hq ha).mp (hs.trans htr)

lemma direct_coefficient_bound {S V D : Matrix ι ι ℝ}
    (hS : S.PosDef) (hV : V.PosSemidef) (hD : D.PosSemidef)
    (hVD : V ≤ D) (hJ : 1 + D = S + V)
    (hA : inverseSqrt S * V * inverseSqrt S ≤ 1) :
    inverseSqrt S * CFC.sqrt (inverseSqrt S * V * inverseSqrt S) * inverseSqrt S ≤
      Real.sqrt 8 • (inverseSqrt (1 + D) *
        CFC.sqrt (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)) * inverseSqrt (1 + D)) := by
  let J := (1 : Matrix ι ι ℝ) + D
  let A := inverseSqrt S * V * inverseSqrt S
  let H := inverseSqrt J * V * inverseSqrt J
  let T := inverseSqrt S * CFC.sqrt J
  have hJp : J.PosDef := Matrix.PosDef.one.add_posSemidef hD
  have hAp : A.PosSemidef := by
    simpa only [A, inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hV.mul_mul_conjTranspose_same (inverseSqrt S)
  have hHp : H.PosSemidef := by
    simpa only [H, inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hV.mul_mul_conjTranspose_same (inverseSqrt J)
  have hTt : T.transpose = CFC.sqrt J * inverseSqrt S := by
    simp only [T, Matrix.transpose_mul, sqrt_transpose, inverseSqrt_transpose]
  have hAe : A = T * H * T.transpose := by
    rw [hTt]
    dsimp [T, H]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt J), sqrt_mul_inverseSqrt hJp, Matrix.one_mul]
    rw [← Matrix.mul_assoc (inverseSqrt J), inverseSqrt_mul_sqrt hJp, Matrix.one_mul]
    simp only [A, Matrix.mul_assoc]
  have hTT : T * T.transpose = 1 + A := by
    rw [hTt]
    dsimp only [T]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (CFC.sqrt J),
      CFC.sqrt_mul_sqrt_self J hJp.posSemidef.nonneg, ← Matrix.mul_assoc]
    change inverseSqrt S * ((1 : Matrix ι ι ℝ) + D) * inverseSqrt S = 1 + A
    rw [hJ, Matrix.mul_add, Matrix.add_mul, inverseSqrt_sandwich hS]
  have hTu : IsUnit T := (inverseSqrt_unit hS).mul
    ((CFC.isUnit_sqrt_iff J hJp.posSemidef.nonneg).mpr hJp.isUnit)
  have hrel := relative_sqrt_bound hTu hHp hAp hAe hTT hA
  have hh := congruence_mono hrel (inverseSqrt J)
  rw [inverseSqrt_transpose, hTt] at hh
  dsimp only [T] at hh
  simp only [← Matrix.mul_assoc, inverseSqrt_mul_sqrt hJp, Matrix.one_mul] at hh
  simp only [Matrix.mul_assoc, sqrt_mul_inverseSqrt hJp, Matrix.mul_one] at hh
  have hp : (inverseSqrt J * D * inverseSqrt J).PosSemidef := by
    simpa only [inverseSqrt_transpose, conjTranspose_eq_transpose_of_trivial]
      using hD.mul_mul_conjTranspose_same (inverseSqrt J)
  have hm : H ≤ inverseSqrt J * D * inverseSqrt J := by
    simpa only [H, inverseSqrt_transpose] using congruence_mono hVD (inverseSqrt J)
  have hsqrt := MatrixEnergy.sqrt_le_sqrt hHp hp hm
  have hout := congruence_mono hsqrt (inverseSqrt J)
  rw [inverseSqrt_transpose] at hout
  have hs := smul_le_smul_of_nonneg_left hout (Real.sqrt_nonneg 8)
  have hleft : inverseSqrt S * CFC.sqrt A * inverseSqrt S ≤
      Real.sqrt 8 • (inverseSqrt J * CFC.sqrt H * inverseSqrt J) := by
    simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] using hh
  exact hleft.trans hs

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.GainScalar
open MatrixEnergy

lemma rate_eq {x : ℝ} (hx : 0 ≤ x) :
    rate x = x ^ (exponent - 1) / (1 + x) ^ exponent := by
  have hx1 : 0 < 1 + x := by positivity
  have hp : (1 + x) ^ exponent = (1 + x) * Real.sqrt (1 + x) := by
    rw [show exponent = 1 + (1 / 2 : ℝ) by norm_num [exponent],
      Real.rpow_add hx1, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [hp, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  rfl

lemma extendedRate_eq {x : ℝ} (hx : 0 ≤ x) : extendedRate x = rate x := by
  simp only [extendedRate, max_eq_right hx]

lemma continuous_extendedRate : Continuous extendedRate := by
  unfold extendedRate rate
  fun_prop (disch := intro x; positivity)

lemma rate_continuousOn : ContinuousOn rate (Set.Ici 0) := by
  refine continuous_extendedRate.continuousOn.congr ?_
  intro x hx
  exact (extendedRate_eq hx).symm

lemma primitive_eq {x : ℝ} (hx : 0 ≤ x) : primitive x = gainPotential x := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hx] at hu
  rw [extendedRate_eq hu.1, rate_eq hu.1]

lemma primitive_derivative (x : ℝ) : HasDerivAt primitive (extendedRate x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_extendedRate.intervalIntegrable 0 x)
    continuous_extendedRate.stronglyMeasurable.stronglyMeasurableAtFilter
    continuous_extendedRate.continuousAt

lemma rate_derivative {x : ℝ} (hx : 0 < x) :
    HasDerivAt rate ((1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x))) x := by
  have hx1 : 0 < 1 + x := by positivity
  have hs : HasDerivAt (fun x : ℝ => Real.sqrt (1 + x)) (1 / (2 * Real.sqrt (1 + x))) x := by
    simpa only [Function.comp_def, mul_one] using (Real.hasDerivAt_sqrt (ne_of_gt hx1)).comp x
      ((hasDerivAt_id x).const_add 1)
  have h := (Real.hasDerivAt_sqrt (ne_of_gt hx)).div
    (((hasDerivAt_id x).const_add 1).mul hs) (by positivity : (1 + x) * Real.sqrt (1 + x) ≠ 0)
  convert! h using 1
  simp only [Pi.mul_apply, id_eq]
  field_simp
  ring_nf
  rw [Real.sq_sqrt hx.le, Real.sq_sqrt hx1.le]
  ring

lemma rate_derivative_lower {x : ℝ} (hx : 0 < x) :
    -1 ≤ (1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x)) := by
  have hx1 : 0 < 1 + x := by positivity
  have hxs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have hys : 0 < Real.sqrt (1 + x) := Real.sqrt_pos.mpr hx1
  have hs : Real.sqrt x ≤ Real.sqrt (1 + x) := Real.sqrt_le_sqrt (by linarith)
  have hprod : x ≤ Real.sqrt x * Real.sqrt (1 + x) := by
    nlinarith [Real.sq_sqrt hx.le]
  have hsq : (1 : ℝ) ≤ (1 + x) ^ 2 := by nlinarith
  have hp : x ≤ Real.sqrt x * Real.sqrt (1 + x) * (1 + x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hsq (mul_nonneg hxs.le hys.le)]
  apply (le_div_iff₀ (by positivity)).mpr
  nlinarith

lemma rate_add_linear_monotone : MonotoneOn (fun x : ℝ => rate x + 2 * x) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (rate_continuousOn.add (continuous_const.mul continuous_id).continuousOn)
    (f' := fun x => (1 - 2 * x) / (2 * Real.sqrt x * (1 + x) ^ 2 * Real.sqrt (1 + x)) + 2)
  · intro x hx
    rw [interior_Ici] at hx
    exact ((rate_derivative hx).fun_add (hasDerivAt_const_mul (x := x) 2)).hasDerivWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have h := rate_derivative_lower hx
    linarith

lemma extendedRate_add_linear_monotone : Monotone (fun x : ℝ => extendedRate x + 2 * x) := by
  intro x y hxy
  change extendedRate x + 2 * x ≤ extendedRate y + 2 * y
  by_cases hx : 0 ≤ x
  · have hy : 0 ≤ y := hx.trans hxy
    simpa only [extendedRate_eq hx, extendedRate_eq hy] using rate_add_linear_monotone hx hy hxy
  · have hxn : x ≤ 0 := le_of_not_ge hx
    by_cases hy : 0 ≤ y
    · have he : extendedRate x = 0 := by simp [extendedRate, max_eq_left hxn, rate]
      have heg : 0 ≤ extendedRate y := by rw [extendedRate_eq hy]; unfold rate; positivity
      rw [he]
      linarith
    · have hyn : y ≤ 0 := le_of_not_ge hy
      simp only [extendedRate, max_eq_left hxn, max_eq_left hyn]
      linarith

lemma convexified_derivative (x : ℝ) :
    HasDerivAt (fun u : ℝ => primitive u + u ^ 2) (extendedRate x + 2 * x) x := by
  simpa using! (primitive_derivative x).fun_add ((hasDerivAt_id x).fun_pow 2)

lemma convexified_convex : ConvexOn ℝ Set.univ (fun x : ℝ => primitive x + x ^ 2) := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (convexified_derivative x).differentiableAt)
  have he : deriv (fun x : ℝ => primitive x + x ^ 2) = (fun x => extendedRate x + 2 * x) := by
    funext x
    exact (convexified_derivative x).deriv
  rw [he]
  exact extendedRate_add_linear_monotone

end EuclideanSteinitz.GainScalar

namespace EuclideanSteinitz.Gain
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma finite_spectrum_continuous (f : ℝ → ℝ) (A : Matrix ι ι ℝ) :
    ContinuousOn f (spectrum ℝ A) := by
  rw [continuousOn_iff_continuous_domRestrict]
  fun_prop

lemma sqrt_eq_cfc_real {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    CFC.sqrt A = cfc Real.sqrt A := by
  rw [CFC.sqrt_eq_rpow, CFC.rpow_eq_cfc_real hA.nonneg]
  congr 1
  funext x
  exact (Real.sqrt_eq_rpow x).symm

lemma inverseSqrt_add_one {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    inverseSqrt (1 + D) = cfc (fun x : ℝ => (Real.sqrt (1 + x))⁻¹) D := by
  have hJ : ((1 : Matrix ι ι ℝ) + D).PosSemidef := Matrix.PosSemidef.one.add hD
  have he : cfc (fun x : ℝ => 1 + x) D = 1 + D := by
    rw [cfc_const_add (1 : ℝ) (fun x : ℝ => x) D continuousOn_id hD.1.isSelfAdjoint,
      cfc_id' ℝ D hD.1.isSelfAdjoint, map_one]
  rw [inverseSqrt, sqrt_eq_cfc_real hJ, ← he, ← cfc_comp Real.sqrt (fun x : ℝ => 1 + x) D]
  rw [cfc_inv (fun x : ℝ => Real.sqrt (1 + x)) D]
  · exact nonsing_inv_eq_ringInverse _
  · intro x hx
    have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
    exact ne_of_gt (Real.sqrt_pos.mpr (by positivity))

lemma relative_rate_coefficient {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    inverseSqrt (1 + D) *
      CFC.sqrt (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)) * inverseSqrt (1 + D) =
      cfc GainScalar.rate D := by
  let f : ℝ → ℝ := fun x => (Real.sqrt (1 + x))⁻¹
  have hfc : ContinuousOn f (spectrum ℝ D) := finite_spectrum_continuous _ _
  have hs : (inverseSqrt (1 + D) * D * inverseSqrt (1 + D)).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial, inverseSqrt_transpose]
      using hD.mul_mul_conjTranspose_same (inverseSqrt (1 + D))
  rw [sqrt_eq_cfc_real hs, inverseSqrt_add_one hD]
  change cfc f D * cfc Real.sqrt (cfc f D * D * cfc f D) * cfc f D = _
  have hmid : cfc f D * D * cfc f D = cfc (fun x => f x * id x * f x) D := by
    rw [cfc_mul (fun x => f x * id x) f D (finite_spectrum_continuous _ _) hfc,
      cfc_mul f id D hfc continuousOn_id, cfc_id ℝ D hD.1.isSelfAdjoint]
  rw [hmid, ← cfc_comp Real.sqrt (fun x => f x * id x * f x) D]
  rw [← cfc_mul f (Real.sqrt ∘ (fun x => f x * id x * f x)) D hfc
    (finite_spectrum_continuous _ _),
    ← cfc_mul (fun x => f x * (Real.sqrt ∘ (fun x => f x * id x * f x)) x) f D
      (finite_spectrum_continuous _ _) hfc]
  apply cfc_congr
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
  have hx1 : 0 < 1 + x := by positivity
  have hs1 : Real.sqrt (1 + x) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hx1)
  have he : f x * id x * f x = x / (1 + x) := by
    dsimp [f]
    field_simp
    rw [Real.sq_sqrt hx1.le]
  simp only [Function.comp_apply, he, Real.sqrt_div hx₀]
  dsimp [f, GainScalar.rate]
  field_simp
  rw [Real.sq_sqrt hx1.le]

lemma direct_coefficient_bound_rate {S V D : Matrix ι ι ℝ}
    (hS : S.PosDef) (hV : V.PosSemidef) (hD : D.PosSemidef)
    (hVD : V ≤ D) (hJ : 1 + D = S + V)
    (hA : inverseSqrt S * V * inverseSqrt S ≤ 1) :
    inverseSqrt S * CFC.sqrt (inverseSqrt S * V * inverseSqrt S) * inverseSqrt S ≤
      Real.sqrt 8 • cfc GainScalar.rate D := by
  simpa only [relative_rate_coefficient hD] using direct_coefficient_bound hS hV hD hVD hJ hA

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Spectral
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_semiconvex_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (f g : ℝ → ℝ)
    (hg : Continuous g) (hder : ∀ x, HasDerivAt f (g x) x)
    (hconv : ConvexOn ℝ Set.univ (fun x : ℝ => f x + x ^ 2)) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (cfc f (A + u • H)).trace)
      (cfc g (A + t • H) * H).trace t := by
  have hf : Continuous f := continuous_iff_continuousAt.mpr (fun x => (hder x).continuousAt)
  have hgf : Continuous (fun x : ℝ => g x + 2 * x) := by fun_prop
  have hdf (x : ℝ) : HasDerivAt (fun u : ℝ => f u + u ^ 2) (g x + 2 * x) x := by
    simpa using! (hder x).fun_add ((hasDerivAt_id x).fun_pow 2)
  have hd := trace_cfc_affine_derivative hA hH (fun x : ℝ => f x + x ^ 2)
    (fun x : ℝ => g x + 2 * x) (T := Set.univ) (S := Set.univ) (Set.mem_univ t)
    (fun _ _ => Set.subset_univ _) (fun x hx y hy =>
      convex_tangent hconv hx hy (hdf y).hasDerivWithinAt)
    (continuous_cfc_affine hA hH hgf).continuousWithinAt
  have hs := trace_cfc_affine_derivative hA hH (fun x : ℝ => x ^ 2)
    (fun x : ℝ => 2 * x) (T := Set.univ) (S := Set.univ) (Set.mem_univ t)
    (fun _ _ => Set.subset_univ _) (fun x _ y _ => by nlinarith [sq_nonneg (x - y)])
    (continuous_cfc_affine hA hH (by fun_prop)).continuousWithinAt
  have hh := (hasDerivWithinAt_univ.mp hd).sub (hasDerivWithinAt_univ.mp hs)
  convert! hh using 1
  · funext u
    dsimp only [Pi.sub_apply]
    rw [cfc_add (A + u • H) f (fun x : ℝ => x ^ 2) hf.continuousOn (by fun_prop), trace_add]
    ring
  · rw [cfc_add (A + t • H) g (fun x : ℝ => 2 * x) hg.continuousOn (by fun_prop), Matrix.add_mul, trace_add]
    ring

lemma trace_gainPotential_affine_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) {T : Set ℝ} {t : ℝ} (ht : t ∈ T)
    (hpos : ∀ u ∈ T, (A + u • H).PosSemidef) :
    HasDerivWithinAt (fun u : ℝ => (cfc MatrixEnergy.gainPotential (A + u • H)).trace)
      (cfc (fun x : ℝ => x ^ (MatrixEnergy.exponent - 1) / (1 + x) ^ MatrixEnergy.exponent)
        (A + t • H) * H).trace T t := by
  have hd := trace_semiconvex_affine_derivative hA hH GainScalar.primitive
    GainScalar.extendedRate GainScalar.continuous_extendedRate
    GainScalar.primitive_derivative GainScalar.convexified_convex t
  have he (u : ℝ) (hu : u ∈ T) :
      cfc GainScalar.primitive (A + u • H) = cfc MatrixEnergy.gainPotential (A + u • H) := by
    apply cfc_congr
    intro x hx
    exact GainScalar.primitive_eq (spectrum_nonneg_of_nonneg (hpos u hu).nonneg hx)
  have hr : cfc GainScalar.extendedRate (A + t • H) =
      cfc (fun x : ℝ => x ^ (MatrixEnergy.exponent - 1) / (1 + x) ^ MatrixEnergy.exponent)
        (A + t • H) := by
    apply cfc_congr
    intro x hx
    have hx₀ := spectrum_nonneg_of_nonneg (hpos t ht).nonneg hx
    rw [GainScalar.extendedRate_eq hx₀, GainScalar.rate_eq hx₀]
  rw [hr] at hd
  exact hd.hasDerivWithinAt.congr (fun u hu => congrArg Matrix.trace (he u hu).symm)
    (congrArg Matrix.trace (he t ht).symm)

end EuclideanSteinitz.Spectral

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma two_rpow_exponent : (2 : ℝ) ^ exponent = Real.sqrt 8 := by
  rw [show exponent = 1 + (1 / 2 : ℝ) by norm_num [exponent],
    Real.rpow_add (by norm_num : (0 : ℝ) < 2), Real.rpow_one, ← Real.sqrt_eq_rpow]
  have h := Real.sqrt_mul (show (0 : ℝ) ≤ 4 by norm_num) 2
  norm_num at h
  exact h.symm

lemma gainConstant_pos : 0 < gainConstant := by
  unfold gainConstant
  exact mul_pos exponent_pos (Real.rpow_pos_of_pos (by norm_num) _)

lemma sandwich_psd {V : Matrix ι ι ℝ} (hV : V.PosSemidef) (S : Matrix ι ι ℝ) :
    (inverseSqrt S * V * inverseSqrt S).PosSemidef := by
  simpa only [conjTranspose_eq_transpose_of_trivial, inverseSqrt_transpose]
    using hV.mul_mul_conjTranspose_same (inverseSqrt S)

lemma sandwich_affine (S V W : Matrix ι ι ℝ) (u : ℝ) :
    inverseSqrt S * (V + u • W) * inverseSqrt S =
      inverseSqrt S * V * inverseSqrt S + u • (inverseSqrt S * W * inverseSqrt S) := by
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]

lemma relativeMoment_derivative {S V W : Matrix ι ι ℝ}
    (hV : V.PosSemidef) (hW : W.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => relativeMoment S (V + u • W))
      (exponent * ((inverseSqrt S * CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S) *
        inverseSqrt S) * W).trace) (Set.Ici 0) t := by
  have hVt : (V + t • W).PosSemidef := hV.add (hW.smul ht)
  have hd := Spectral.trace_rpow_affine_derivative (sandwich_psd hV S).1
    (sandwich_psd hW S).1 (show (1 : ℝ) ≤ exponent by norm_num [exponent])
    (T := Set.Ici 0) ht (fun u hu => by
      rw [← sandwich_affine]
      exact sandwich_psd (hV.add (hW.smul hu)) S)
  have hh : cfc (fun x : ℝ => x ^ (exponent - 1))
      (inverseSqrt S * V * inverseSqrt S + t • (inverseSqrt S * W * inverseSqrt S)) =
      CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S) := by
    rw [← sandwich_affine, sqrt_eq_cfc_real (sandwich_psd hVt S)]
    congr 1
    funext x
    rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], Real.sqrt_eq_rpow]
  rw [hh] at hd
  convert! hd using 1
  · funext u
    simp only [relativeMoment, sandwich_affine]
  · congr 1
    let A := CFC.sqrt (inverseSqrt S * (V + t • W) * inverseSqrt S)
    change ((inverseSqrt S * A * inverseSqrt S) * W).trace =
      (A * (inverseSqrt S * W * inverseSqrt S)).trace
    calc
      _ = (inverseSqrt S * (A * inverseSqrt S * W)).trace := by
        simp only [Matrix.mul_assoc]
      _ = ((A * inverseSqrt S * W) * inverseSqrt S).trace := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [Matrix.mul_assoc]

lemma gainValue_derivative {D W : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (hW : W.PosSemidef) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivWithinAt (fun u => gainValue (D + u • W))
      (cfc GainScalar.rate (D + t • W) * W).trace (Set.Ici 0) t := by
  have hd := Spectral.trace_gainPotential_affine_derivative hD.1 hW.1
    (T := Set.Ici 0) ht (fun u hu => hD.add (hW.smul hu))
  have he : cfc (fun x : ℝ => x ^ (exponent - 1) / (1 + x) ^ exponent) (D + t • W) =
      cfc GainScalar.rate (D + t • W) := by
    apply cfc_congr
    intro x hx
    exact (GainScalar.rate_eq (spectrum_nonneg_of_nonneg (hD.add (hW.smul ht)).nonneg hx)).symm
  rwa [he] at hd

lemma rate_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    (cfc GainScalar.rate D).PosSemidef := by
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hD.nonneg hx
  unfold GainScalar.rate
  positivity

lemma gainValue_monotone {D W : Matrix ι ι ℝ}
    (hD : D.PosSemidef) (hW : W.PosSemidef) :
    MonotoneOn (fun u : ℝ => gainValue (D + u • W)) (Set.Ici 0) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
    (fun u hu => (gainValue_derivative hD hW hu).continuousWithinAt)
    (f' := fun t => (cfc GainScalar.rate (D + t • W) * W).trace)
  · intro t ht
    exact (gainValue_derivative hD hW (interior_subset ht)).mono interior_subset
  · intro t ht
    exact MatrixEnergy.trace_mul_nonneg (rate_nonneg (hD.add (hW.smul (interior_subset ht)))) hW

lemma gain_derivative_bound {Z V W : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hW : W.PosSemidef)
    (hG : relativeMoment (1 + Z) V ≤ 1) :
    exponent * ((inverseSqrt (1 + Z) *
      CFC.sqrt (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z)) * inverseSqrt (1 + Z)) * W).trace ≤
      gainConstant * (cfc GainScalar.rate (Z + V) * W).trace := by
  have hS : ((1 : Matrix ι ι ℝ) + Z).PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hA : inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z) ≤ 1 := by
    have ht : (cfc (fun x : ℝ => x ^ exponent)
        (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z))).trace ≤ (1 : ℝ) ^ exponent := by
      simpa only [Real.one_rpow, relativeMoment] using hG
    simpa only [one_smul] using trace_power_bound (sandwich_psd hV (1 + Z)) exponent_pos
      (show (0 : ℝ) ≤ 1 by norm_num) ht
  have hVD : V ≤ Z + V := by
    exact le_add_of_nonneg_left hZ.nonneg
  have hc := direct_coefficient_bound_rate hS hV (hZ.add hV) hVD (by abel) hA
  have ht := MatrixEnergy.trace_mul_mono_right hc hW
  simp only [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul] at ht
  have h := mul_le_mul_of_nonneg_left ht exponent_pos.le
  simpa only [gainConstant, two_rpow_exponent, mul_assoc] using h

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz

lemma conditional_derivative_comparison {f f' g g' : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (hg : ContinuousOn g (Set.Icc 0 1))
    (hfd : ∀ x ∈ Set.Ico 0 1, HasDerivWithinAt f (f' x) (Set.Ici x) x)
    (hgd : ∀ x ∈ Set.Ico 0 1, HasDerivWithinAt g (g' x) (Set.Ici x) x)
    (hbudget : ∀ x ∈ Set.Icc 0 1, f 0 + g x - g 0 ≤ 1 / 4)
    (hbound : ∀ x ∈ Set.Ico 0 1, f x ≤ 1 → f' x ≤ g' x) :
    ∀ x ∈ Set.Icc 0 1, f x ≤ f 0 + g x - g 0 := by
  have hB : ContinuousOn (fun x => f 0 + g x - g 0 + x / 2) (Set.Icc 0 1) :=
    ((continuousOn_const.add hg).sub continuousOn_const).add
      (continuous_id.div_const 2).continuousOn
  have hBd (x : ℝ) (hx : x ∈ Set.Ico 0 1) :
      HasDerivWithinAt (fun x => f 0 + g x - g 0 + x / 2) (g' x + 1 / 2) (Set.Ici x) x := by
    simpa using! (((hgd x hx).const_add (f 0)).sub_const (g 0)).add
      ((hasDerivAt_id x).div_const 2).hasDerivWithinAt
  have hpre := image_le_of_deriv_right_lt_deriv_boundary' hf hfd
    (B := fun x => f 0 + g x - g 0 + x / 2) (B' := fun x => g' x + 1 / 2)
    (by simp) hB hBd (fun x hx he => by
      have hb := hbudget x ⟨hx.1, hx.2.le⟩
      have hx1 : f x ≤ 1 := by rw [he]; linarith [hx.2]
      linarith [hbound x hx hx1])
  have hfull (x : ℝ) (hx : x ∈ Set.Ico 0 1) : f' x ≤ g' x := by
    apply hbound x hx
    have hp := hpre (show x ∈ Set.Icc 0 1 from ⟨hx.1, hx.2.le⟩)
    have hb := hbudget x ⟨hx.1, hx.2.le⟩
    linarith [hx.2]
  apply fun x hx => image_le_of_deriv_right_le_deriv_boundary hf hfd
    (B := fun x => f 0 + g x - g 0) (B' := g') (by simp)
    ((continuousOn_const.add hg).sub continuousOn_const)
    (fun x hx => by simpa using! ((hgd x hx).const_add (f 0)).sub_const (g 0)) hfull hx

end EuclideanSteinitz

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_gain {Z V W : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hW : W.PosSemidef)
    (hbudget : relativeMoment (1 + Z) V +
      gainConstant * (gainValue (Z + V + W) - gainValue (Z + V)) ≤ 1 / 4) :
    relativeMoment (1 + Z) (V + W) ≤ relativeMoment (1 + Z) V +
      gainConstant * (gainValue (Z + V + W) - gainValue (Z + V)) := by
  let f : ℝ → ℝ := fun t => relativeMoment (1 + Z) (V + t • W)
  let f' : ℝ → ℝ := fun t => exponent * ((inverseSqrt (1 + Z) *
    CFC.sqrt (inverseSqrt (1 + Z) * (V + t • W) * inverseSqrt (1 + Z)) *
      inverseSqrt (1 + Z)) * W).trace
  let g : ℝ → ℝ := fun t => gainConstant * gainValue (Z + V + t • W)
  let g' : ℝ → ℝ := fun t => gainConstant * (cfc GainScalar.rate (Z + V + t • W) * W).trace
  have hfd (x : ℝ) (hx : 0 ≤ x) : HasDerivWithinAt f (f' x) (Set.Ici 0) x :=
    relativeMoment_derivative hV hW hx
  have hgd (x : ℝ) (hx : 0 ≤ x) : HasDerivWithinAt g (g' x) (Set.Ici 0) x :=
    (gainValue_derivative (hZ.add hV) hW hx).const_mul gainConstant
  have hbound : ∀ x ∈ Set.Ico 0 1, f x ≤ 1 → f' x ≤ g' x := by
    intro x hx hfx
    have hb := gain_derivative_bound hZ (hV.add (hW.smul hx.1)) hW hfx
    simpa only [f', g', add_assoc] using hb
  have hbud : ∀ x ∈ Set.Icc 0 1, f 0 + g x - g 0 ≤ 1 / 4 := by
    intro x hx
    have hm := gainValue_monotone (hZ.add hV) hW hx.1 (show (0 : ℝ) ≤ 1 by norm_num) hx.2
    simp only [one_smul] at hm
    have hc := mul_le_mul_of_nonneg_left hm gainConstant_pos.le
    dsimp only [f, g]
    simp only [zero_smul, add_zero]
    linarith
  have hf : ContinuousOn f (Set.Icc 0 1) := fun x hx =>
    (hfd x hx.1).continuousWithinAt.mono (fun _ hu => hu.1)
  have hg : ContinuousOn g (Set.Icc 0 1) := fun x hx =>
    (hgd x hx.1).continuousWithinAt.mono (fun _ hu => hu.1)
  have hc := EuclideanSteinitz.conditional_derivative_comparison hf hg
    (fun x hx => (hfd x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1))
    (fun x hx => (hgd x hx.1).mono (Set.Ici_subset_Ici.mpr hx.1)) hbud hbound
    1 (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num)
  simpa only [f, g, zero_smul, one_smul, add_zero, sub_eq_add_neg, mul_add, mul_neg,
    add_assoc] using hc

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_zero (S : Matrix ι ι ℝ) : relativeMoment S 0 = 0 := by
  simp only [relativeMoment, Matrix.mul_zero, Matrix.zero_mul, cfc_apply_zero,
    Real.zero_rpow (ne_of_gt exponent_pos), map_zero, Matrix.trace_zero]

lemma relativeMoment_contraction {Z V C : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) (hC : C * C.transpose ≤ 1) :
    relativeMoment (1 + C * Z * C.transpose) (C * V * C.transpose) ≤
      relativeMoment (1 + Z) V := by
  let S : Matrix ι ι ℝ := 1 + Z
  let Z' := C * Z * C.transpose
  let S' : Matrix ι ι ℝ := 1 + Z'
  let A := inverseSqrt S * V * inverseSqrt S
  let T := inverseSqrt S' * C * CFC.sqrt S
  have hS : S.PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hZ' : Z'.PosSemidef := by
    simpa only [Z', conjTranspose_eq_transpose_of_trivial] using hZ.mul_mul_conjTranspose_same C
  have hS' : S'.PosDef := Matrix.PosDef.one.add_posSemidef hZ'
  have hTt : T.transpose = CFC.sqrt S * C.transpose * inverseSqrt S' := by
    simp only [T, Matrix.transpose_mul, sqrt_transpose, inverseSqrt_transpose, Matrix.mul_assoc]
  have he : inverseSqrt S' * (C * V * C.transpose) * inverseSqrt S' = T * A * T.transpose := by
    rw [hTt]
    dsimp only [T, A]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt S), sqrt_mul_inverseSqrt hS, Matrix.one_mul]
    rw [← Matrix.mul_assoc (inverseSqrt S), inverseSqrt_mul_sqrt hS, Matrix.one_mul]
  have hCS : C * S * C.transpose ≤ S' := by
    simp only [S, S', Z', Matrix.mul_add, Matrix.mul_one, Matrix.add_mul]
    exact add_le_add hC le_rfl
  have hTT : T * T.transpose ≤ 1 := by
    have hh := congruence_mono hCS (inverseSqrt S')
    rw [inverseSqrt_transpose, inverseSqrt_sandwich hS'] at hh
    convert! hh using 1
    rw [hTt]
    dsimp only [T]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (CFC.sqrt S), CFC.sqrt_mul_sqrt_self S hS.posSemidef.nonneg]
  have hb := Spectral.trace_rpow_contraction (sandwich_psd hV S) hTT
    (show (1 : ℝ) ≤ exponent by norm_num [exponent])
  unfold relativeMoment
  change (cfc (fun x : ℝ => x ^ exponent)
    (inverseSqrt S' * (C * V * C.transpose) * inverseSqrt S')).trace ≤ _
  rw [he]
  exact hb

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma Move.old_add (p : Move ι) (A B : Matrix ι ι ℝ) : p.old (A + B) = p.old A + p.old B := by
  simp only [Move.old, Matrix.mul_add, Matrix.add_mul]

omit [DecidableEq ι] in
lemma Move.old_psd (p : Move ι) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (p.old A).PosSemidef := by
  simpa only [Move.old, conjTranspose_eq_transpose_of_trivial]
    using hA.mul_mul_conjTranspose_same p.contract

lemma Move.next_psd {p : Move ι} (hp : p.Admissible) {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (p.next A).PosSemidef := (p.old_psd hA).add hp.2

lemma Move.gain_nonneg {p : Move ι} (hp : p.Admissible) {D : Matrix ι ι ℝ} (hD : D.PosSemidef) :
    0 ≤ gainValue (p.next D) - gainValue (p.old D) := by
  have h := gainValue_monotone (p.old_psd hD) hp.2 (show (0 : ℝ) ≤ 0 by rfl)
    (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [Move.next, zero_smul, one_smul, add_zero, sub_nonneg] using h

lemma gainCost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : 0 ≤ gainCost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hpa := hp p (List.mem_cons_self ..)
    exact add_nonneg (p.gain_nonneg hpa hD)
      (ih (p.next_psd hpa hD) (fun q hq => hp q (List.mem_cons_of_mem p hq)))

lemma follow_psd {Z V : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hV : V.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) :
    (follow Z V ps).1.PosSemidef ∧ (follow Z V ps).2.PosSemidef := by
  induction ps generalizing Z V with
  | nil => exact ⟨hZ, hV⟩
  | cons p ps ih =>
    exact ih (p.old_psd hZ) (p.next_psd (hp p (List.mem_cons_self ..)) hV)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))

lemma relativeMoment_path {Z V : Matrix ι ι ℝ} (hZ : Z.PosSemidef) (hV : V.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible)
    (hbudget : relativeMoment (1 + Z) V + gainConstant * gainCost (Z + V) ps ≤ 1 / 4) :
    relativeMoment (1 + (follow Z V ps).1) (follow Z V ps).2 ≤
      relativeMoment (1 + Z) V + gainConstant * gainCost (Z + V) ps := by
  induction ps generalizing Z V with
  | nil => simp only [follow, gainCost, mul_zero, add_zero, le_refl]
  | cons p ps ih =>
    have hpa := hp p (List.mem_cons_self ..)
    have hps : ∀ q ∈ ps, q.Admissible := fun q hq => hp q (List.mem_cons_of_mem p hq)
    have hz := p.old_psd hZ
    have hv := p.old_psd hV
    have hnew := p.next_psd hpa hV
    have he : p.next (Z + V) = p.old Z + p.next V := by
      simp only [Move.next, p.old_add, add_assoc]
    have hc := relativeMoment_contraction hZ hV hpa.1
    change relativeMoment (1 + p.old Z) (p.old V) ≤ relativeMoment (1 + Z) V at hc
    have htail := gainCost_nonneg (p.next_psd hpa (hZ.add hV)) hps
    have hb : relativeMoment (1 + p.old Z) (p.old V) +
        gainConstant * (gainValue (p.old Z + p.old V + p.gain) - gainValue (p.old Z + p.old V)) ≤ 1 / 4 := by
      simp only [gainCost, Move.next, p.old_add] at hbudget htail
      nlinarith [gainConstant_pos]
    have hg := relativeMoment_gain hz hv hpa.2 hb
    change relativeMoment (1 + p.old Z) (p.next V) ≤ _ at hg
    simp only [Move.next] at hg
    have hbudget' : relativeMoment (1 + p.old Z) (p.next V) +
        gainConstant * gainCost (p.old Z + p.next V) ps ≤ 1 / 4 := by
      rw [← he]
      simp only [gainCost] at hbudget
      simp only [Move.next, p.old_add] at hbudget ⊢
      linarith
    have hi := ih hz hnew hps hbudget'
    change relativeMoment (1 + (follow (p.old Z) (p.next V) ps).1)
      (follow (p.old Z) (p.next V) ps).2 ≤ _
    rw [← he] at hi
    simp only [gainCost]
    simp only [Move.next, p.old_add] at hi hg ⊢
    linarith

end EuclideanSteinitz.Gain

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Coefficients
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered coefficients and their quadratic energy bounds. -/

namespace EuclideanSteinitz.Gain
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma relativeMoment_controls_gain {Z V : Matrix ι ι ℝ}
    (hZ : Z.PosSemidef) (hV : V.PosSemidef) {q : ℝ} (hq : 0 ≤ q)
    (hG : relativeMoment (1 + Z) V ≤ q ^ exponent) :
    V ≤ q • (1 + Z) := by
  have hS : ((1 : Matrix ι ι ℝ) + Z).PosDef := Matrix.PosDef.one.add_posSemidef hZ
  have hA := trace_power_bound (sandwich_psd hV (1 + Z)) exponent_pos hq hG
  have h := congruence_mono hA (CFC.sqrt (1 + Z))
  rw [sqrt_transpose] at h
  have he : CFC.sqrt (1 + Z) * (inverseSqrt (1 + Z) * V * inverseSqrt (1 + Z)) *
      CFC.sqrt (1 + Z) = V := by
    simp only [← Matrix.mul_assoc, sqrt_mul_inverseSqrt hS, Matrix.one_mul]
    rw [Matrix.mul_assoc, inverseSqrt_mul_sqrt hS, Matrix.mul_one]
  rw [he] at h
  simpa only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    CFC.sqrt_mul_sqrt_self _ hS.posSemidef.nonneg] using h

lemma accumulated_gain_bound {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ}
    (hcost : gainCost Y ps ≤ E) (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let q := (gainConstant * E) ^ (1 / exponent)
    0 ≤ q ∧ q < 1 / 4 ∧
    (follow Y 0 ps).2 ≤ q • (1 + (follow Y 0 ps).1) ∧
    (follow Y 0 ps).2 ≤ q • (1 + ((follow Y 0 ps).1 + (follow Y 0 ps).2)) := by
  have hE : 0 ≤ E := (gainCost_nonneg hY hp).trans hcost
  have hc : 0 ≤ gainConstant * E := mul_nonneg gainConstant_pos.le hE
  have hce : gainConstant * E ≤ 1 / 16 := by
    have hd := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) gainConstant_pos)).mp hsmall
    nlinarith
  let q := (gainConstant * E) ^ (1 / exponent)
  have hq : 0 ≤ q := Real.rpow_nonneg hc _
  have hpow : q ^ exponent = gainConstant * E := by
    dsimp only [q]
    rw [← Real.rpow_mul hc]
    rw [one_div_mul_cancel (ne_of_gt exponent_pos), Real.rpow_one]
  have hquarter : (1 / 16 : ℝ) < (1 / 4 : ℝ) ^ exponent := by
    rw [show (1 / 4 : ℝ) = (1 / 2 : ℝ) ^ 2 by norm_num, ← Real.rpow_natCast_mul (by norm_num)]
    norm_num [exponent, Real.rpow_natCast]
  have hqsmall : q < 1 / 4 := by
    apply (Real.rpow_lt_rpow_iff hq (by norm_num) exponent_pos).mp
    rw [hpow]
    exact hce.trans_lt hquarter
  have hb : relativeMoment (1 + Y) 0 + gainConstant * gainCost (Y + 0) ps ≤ 1 / 4 := by
    rw [relativeMoment_zero, zero_add, add_zero]
    have hh := mul_le_mul_of_nonneg_left hcost gainConstant_pos.le
    linarith
  have hg := relativeMoment_path hY Matrix.PosSemidef.zero hp hb
  rw [relativeMoment_zero, zero_add, add_zero] at hg
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hG : relativeMoment (1 + (follow Y 0 ps).1) (follow Y 0 ps).2 ≤ q ^ exponent := by
    rw [hpow]
    exact hg.trans (mul_le_mul_of_nonneg_left hcost gainConstant_pos.le)
  have hbound := relativeMoment_controls_gain hpsd.1 hpsd.2 hq hG
  refine ⟨hq, hqsmall, hbound, hbound.trans ?_⟩
  apply smul_le_smul_of_nonneg_left _ hq
  exact add_le_add le_rfl (le_add_of_nonneg_right hpsd.2.nonneg)

end EuclideanSteinitz.Gain

namespace EuclideanSteinitz.PotentialScalar
open MatrixEnergy

lemma continuous_rate : Continuous rate := by
  unfold rate
  apply Continuous.min Real.continuous_sqrt
  apply Continuous.pow
  apply Continuous.inv₀ (continuous_const.max continuous_id)
  intro x
  exact ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left _ _))

lemma rate_nonneg (x : ℝ) : 0 ≤ rate x := le_min (Real.sqrt_nonneg _) (sq_nonneg _)

lemma rate_small {x : ℝ} (hx : x ≤ 1) : rate x = Real.sqrt x := by
  unfold rate
  rw [max_eq_left hx]
  norm_num only [inv_one, one_pow]
  exact min_eq_left (Real.sqrt_le_one.mpr hx)

lemma rate_large {x : ℝ} (hx : 1 ≤ x) : rate x = x⁻¹ ^ 2 := by
  unfold rate
  rw [max_eq_right hx]
  apply min_eq_right
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx
  have his : x⁻¹ ^ 2 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr hx0.le) hi
  exact his.trans (Real.one_le_sqrt.mpr hx)

lemma rate_eq {x : ℝ} (hx : 0 ≤ x) : rate x = weight x / x := by
  by_cases h1 : x ≤ 1
  · rw [rate_small h1, integrand_of_le_one hx h1, Real.sqrt_eq_rpow]
  · have h1' : 1 ≤ x := (lt_of_not_ge h1).le
    rw [rate_large h1', integrand_of_one_le h1']
    rw [show (-2 : ℝ) = -1 * 2 by norm_num, Real.rpow_mul hx, Real.rpow_neg_one,
      Real.rpow_two]

lemma rate_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : rate x = 0 := by
  rw [rate_small (hx.trans (by norm_num)), Real.sqrt_eq_zero_of_nonpos hx]

lemma primitive_eq {x : ℝ} (hx : 0 ≤ x) : primitive x = potential x := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hx] at hu
  exact rate_eq hu.1

lemma primitive_derivative (x : ℝ) : HasDerivAt primitive (rate x) x := by
  exact intervalIntegral.integral_hasDerivAt_right
    (continuous_rate.intervalIntegrable 0 x)
    continuous_rate.stronglyMeasurable.stronglyMeasurableAtFilter continuous_rate.continuousAt

lemma primitive_monotone : Monotone primitive := by
  apply monotone_of_hasDerivAt_nonneg primitive_derivative
  exact rate_nonneg

lemma primitive_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : primitive x = 0 := by
  unfold primitive
  calc
    _ = ∫ u in (0 : ℝ)..x, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_ge hx] at hu
      exact rate_zero_of_nonpos hu.2
    _ = 0 := by simp

lemma large_add_linear_monotone : MonotoneOn (fun x : ℝ => x⁻¹ ^ 2 + 2 * x) (Set.Ici 1) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 1)
    (f' := fun x => -2 * x⁻¹ ^ 3 + 2)
  · have hne : ∀ x ∈ Set.Ici (1 : ℝ), x ≠ 0 := fun x hx => ne_of_gt (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hx)
    exact (((continuousOn_id.inv₀ hne).pow 2).add
      (continuous_const.mul continuous_id).continuousOn)
  · intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hxn : x ≠ 0 := ne_of_gt (by linarith : 0 < x)
    have h := (((hasDerivAt_id x).inv hxn).fun_pow 2).fun_add (hasDerivAt_const_mul (x := x) 2)
    convert! h.hasDerivWithinAt using 1
    simp
    ring
  · intro x hx
    rw [interior_Ici] at hx
    change 1 < x at hx
    have hi : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx.le
    have hp : x⁻¹ ^ 3 ≤ 1 := pow_le_one₀ (inv_nonneg.mpr (by linarith)) hi
    linarith

lemma rate_add_linear_monotone : Monotone (fun x : ℝ => rate x + 2 * x) := by
  intro x y hxy
  change rate x + 2 * x ≤ rate y + 2 * y
  by_cases hx : x ≤ 1
  · by_cases hy : y ≤ 1
    · rw [rate_small hx, rate_small hy]
      exact add_le_add (Real.sqrt_le_sqrt hxy) (by linarith)
    · have hy' : 1 ≤ y := (lt_of_not_ge hy).le
      have hl : rate x + 2 * x ≤ 3 := by
        rw [rate_small hx]
        have hs := Real.sqrt_le_one.mpr hx
        linarith
      have hr := large_add_linear_monotone (show (1 : ℝ) ≤ 1 by norm_num) hy' hy'
      rw [rate_large hy']
      norm_num only [inv_one, one_pow, mul_one, show (1 : ℝ) + 2 = 3 by norm_num] at hr
      exact hl.trans hr
  · have hx' : 1 ≤ x := (lt_of_not_ge hx).le
    have hy' := hx'.trans hxy
    rw [rate_large hx', rate_large hy']
    exact large_add_linear_monotone hx' hy' hxy

lemma convexified_derivative (x : ℝ) :
    HasDerivAt (fun u : ℝ => primitive u + u ^ 2) (rate x + 2 * x) x := by
  simpa using! (primitive_derivative x).fun_add ((hasDerivAt_id x).fun_pow 2)

lemma convexified_convex : ConvexOn ℝ Set.univ (fun x : ℝ => primitive x + x ^ 2) := by
  apply Monotone.convexOn_univ_of_deriv (fun x => (convexified_derivative x).differentiableAt)
  have he : deriv (fun x : ℝ => primitive x + x ^ 2) = (fun x => rate x + 2 * x) := by
    funext x
    exact (convexified_derivative x).deriv
  rw [he]
  exact rate_add_linear_monotone

end EuclideanSteinitz.PotentialScalar

namespace EuclideanSteinitz.PotentialScalar
open MatrixEnergy

lemma sizeWeight_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : sizeWeight x = Real.sqrt x := by
  rw [sizeWeight, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  rcases hx.eq_or_lt with rfl | hx
  · norm_num
  · apply min_eq_left
    exact (Real.sqrt_le_one.mpr hx1).trans ((one_le_inv₀ hx).mpr hx1)

lemma sizeWeight_large {x : ℝ} (hx : 1 ≤ x) : sizeWeight x = x⁻¹ := by
  rw [sizeWeight, show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  exact min_eq_right ((inv_le_one_of_one_le₀ hx).trans (Real.one_le_sqrt.mpr hx))

lemma primitive_small {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    primitive x = (2 / 3 : ℝ) * x * Real.sqrt x := by
  rw [primitive_eq hx, potential_small hx hx1,
    show exponent = (1 / 2 : ℝ) + 1 by norm_num [exponent],
    Real.rpow_add_one' hx (by norm_num : (1 / 2 : ℝ) + 1 ≠ 0), ← Real.sqrt_eq_rpow]
  ring

lemma primitive_nonneg (x : ℝ) : 0 ≤ primitive x := by
  by_cases hx : 0 ≤ x
  · have h := primitive_monotone hx
    simpa only [primitive_zero_of_nonpos (le_refl (0 : ℝ))] using h
  · rw [primitive_zero_of_nonpos (le_of_not_ge hx)]

lemma primitive_sub_le {x z M : ℝ} (hzx : z ≤ x)
    (hM : ∀ u ∈ Set.Icc z x, rate u ≤ M) : primitive x - primitive z ≤ (x - z) * M := by
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := MeasureTheory.volume)
    (continuous_rate.intervalIntegrable 0 z) (continuous_rate.intervalIntegrable z x)
  have hi := intervalIntegral.integral_mono_on hzx (continuous_rate.intervalIntegrable z x)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => M) MeasureTheory.volume z x) hM
  simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
  unfold primitive
  linarith

lemma rate_le_inverse_sq {u : ℝ} (hu : 0 < u) : rate u ≤ u⁻¹ ^ 2 := by
  apply (min_le_right _ _).trans
  exact pow_le_pow_left₀ (by positivity)
    (inv_le_inv₀ (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 u)) hu |>.mpr
      (le_max_right _ _)) 2

lemma direct_scalar_bound {x q : ℝ} (hx : 0 ≤ x) (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4) :
    primitive x - primitive ((1 - q) * x - q) ≤ 8 * q * sizeWeight x := by
  let z := (1 - q) * x - q
  have hzx : z ≤ x := by dsimp [z]; nlinarith
  have hd : x - z = q * (1 + x) := by dsimp [z]; ring
  by_cases hsmall : x ≤ 4 * q
  · have hx1 : x ≤ 1 := by linarith
    rw [sizeWeight_small hx hx1, primitive_small hx hx1]
    have hp := primitive_nonneg z
    have hm := mul_le_mul_of_nonneg_right hsmall (Real.sqrt_nonneg x)
    have hqs := mul_nonneg hq (Real.sqrt_nonneg x)
    change _ - primitive z ≤ _
    nlinarith
  · have hlarge : 4 * q < x := lt_of_not_ge hsmall
    have hx0 : 0 < x := by linarith
    have hhalf : x / 2 ≤ z := by
      dsimp [z]
      have hqx := mul_le_mul_of_nonneg_right hq1 hx
      nlinarith
    by_cases hx1 : x ≤ 1
    · have hi := primitive_sub_le hzx (M := Real.sqrt x) (fun u hu =>
        (min_le_left _ _).trans (Real.sqrt_le_sqrt hu.2))
      rw [hd] at hi
      rw [sizeWeight_small hx hx1]
      have hm := mul_le_mul_of_nonneg_left hx1 hq
      have hs := Real.sqrt_nonneg x
      change _ - primitive z ≤ _
      nlinarith [mul_nonneg (by linarith : 0 ≤ 8 * q - q * (1 + x)) hs]
    · have hx1' : 1 ≤ x := (lt_of_not_ge hx1).le
      have hrate : ∀ u ∈ Set.Icc z x, rate u ≤ 4 * x⁻¹ ^ 2 := by
        intro u hu
        have hu0 : 0 < u := lt_of_lt_of_le (by linarith : 0 < x / 2) (hhalf.trans hu.1)
        have hi : u⁻¹ ≤ 2 * x⁻¹ := by
          calc
            u⁻¹ ≤ (x / 2)⁻¹ := (inv_le_inv₀ hu0 (half_pos hx0)).mpr (hhalf.trans hu.1)
            _ = 2 * x⁻¹ := by simp [div_eq_mul_inv]
        have hh := pow_le_pow_left₀ (inv_nonneg.mpr hu0.le) hi 2
        exact (rate_le_inverse_sq hu0).trans (by nlinarith)
      have hi := primitive_sub_le hzx hrate
      rw [hd] at hi
      rw [sizeWeight_large hx1']
      change _ - primitive z ≤ _
      have he : x * x⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hx0)
      have him : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hx1'
      have hin : 0 ≤ x⁻¹ := inv_nonneg.mpr hx
      have hs : x * x⁻¹ ^ 2 = x⁻¹ := by calc
        _ = (x * x⁻¹) * x⁻¹ := by ring
        _ = x⁻¹ := by rw [he, one_mul]
      have hsq : x⁻¹ ^ 2 ≤ x⁻¹ := by nlinarith
      have hc := mul_le_mul_of_nonneg_left hsq (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hq)
      nlinarith

end EuclideanSteinitz.PotentialScalar

namespace EuclideanSteinitz.Spectral
open Matrix MatrixEnergy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma trace_primitive_monotone {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (_hB : B.IsHermitian) (hAB : A ≤ B) :
    (cfc PotentialScalar.primitive A).trace ≤ (cfc PotentialScalar.primitive B).trace := by
  have hH := Matrix.le_iff.mp hAB
  have hd (t : ℝ) := trace_semiconvex_affine_derivative hA hH.1
    PotentialScalar.primitive PotentialScalar.rate PotentialScalar.continuous_rate
    PotentialScalar.primitive_derivative PotentialScalar.convexified_convex t
  have hm := monotone_of_hasDerivAt_nonneg hd (fun t => by
    apply MatrixEnergy.trace_mul_nonneg _ hH
    apply Matrix.nonneg_iff_posSemidef.mp
    exact cfc_nonneg (fun x _ => PotentialScalar.rate_nonneg x))
  have h := hm (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using h

lemma cfc_primitive_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    cfc PotentialScalar.primitive A = cfc potential A := by
  apply cfc_congr
  intro x hx
  exact PotentialScalar.primitive_eq (spectrum_nonneg_of_nonneg hA.nonneg hx)

lemma trace_potential_direct {X Z : Matrix ι ι ℝ} (hX : X.PosSemidef) (hZ : Z.PosSemidef)
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1 / 4)
    (hXZ : X - Z ≤ q • (1 + X)) :
    (cfc potential X).trace - (cfc potential Z).trace ≤ 8 * q * (cfc sizeWeight X).trace := by
  let A : Matrix ι ι ℝ := (1 - q) • X - q • 1
  have hA : A.IsHermitian := (hX.1.smul (IsSelfAdjoint.all _)).sub (isHermitian_one.smul (IsSelfAdjoint.all _))
  have hAZ : A ≤ Z := by
    apply Matrix.le_iff.mpr
    have hh := Matrix.le_iff.mp hXZ
    convert! hh using 1
    dsimp only [A]
    module
  have hm := trace_primitive_monotone hA hZ.1 hAZ
  have he : cfc (fun x : ℝ => (1 - q) * x - q) X = A := by
    rw [cfc_sub (fun x : ℝ => (1 - q) * x) (fun _ => q) X (by fun_prop) (by fun_prop),
      cfc_const_mul (1 - q) (fun x : ℝ => x) X (by fun_prop), cfc_id' ℝ X hX.1.isSelfAdjoint,
      cfc_const q X hX.1.isSelfAdjoint, Algebra.algebraMap_eq_smul_one]
  have hf : Continuous PotentialScalar.primitive := continuous_iff_continuousAt.mpr
    (fun x => (PotentialScalar.primitive_derivative x).continuousAt)
  have hcomp : cfc (fun x : ℝ => PotentialScalar.primitive ((1 - q) * x - q)) X =
      cfc PotentialScalar.primitive A := by
    rw [← he]
    exact cfc_comp PotentialScalar.primitive (fun x : ℝ => (1 - q) * x - q) X
      hX.1.isSelfAdjoint hf.continuousOn (by fun_prop)
  have hb : (cfc PotentialScalar.primitive X).trace - (cfc PotentialScalar.primitive A).trace ≤
      8 * q * (cfc sizeWeight X).trace := by
    rw [← hcomp, trace_cfc hX.1, trace_cfc hX.1, trace_cfc hX.1,
      ← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact PotentialScalar.direct_scalar_bound (hX.eigenvalues_nonneg i) hq hq1
  rw [cfc_primitive_eq hX] at hb
  rw [cfc_primitive_eq hZ] at hm
  linarith

end EuclideanSteinitz.Spectral

namespace EuclideanSteinitz.Endpoint
open Matrix MatrixEnergy Spectral
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
lemma diag_le {A B : Matrix ι ι ℝ} (hAB : A ≤ B) (i : ι) : A i i ≤ B i i := by
  have h := (Matrix.le_iff.mp hAB).diag_nonneg (i := i)
  simpa only [Matrix.sub_apply, sub_nonneg] using h

lemma diagonalize {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A * hA.eigenvectorUnitary =
      diagonal hA.eigenvalues := by
  conv_lhs => arg 1; arg 2; rw [real_spectral hA]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma inverse_spectral {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    A⁻¹ = (hA.1.eigenvectorUnitary : Matrix ι ι ℝ) *
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) *
      (hA.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose := by
  rw [nonsing_inv_eq_ringInverse, ← cfc_ringInverse_id (R := ℝ) A hA.isUnit hA.1.isSelfAdjoint]
  exact real_cfc hA.1 _

lemma sandwich_diagonal_apply (M : Matrix ι ι ℝ) (w : ι → ℝ) (i : ι) :
    (M * diagonal w * M.transpose) i i = ∑ j, (M i j) ^ 2 * w j := by
  simp only [Matrix.mul_apply (M := M * diagonal w), mul_diagonal, transpose_apply]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma overlap_conjugate {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B * hA.eigenvectorUnitary =
      (overlapBasis hA hB : Matrix ι ι ℝ) * diagonal hB.eigenvalues *
        (overlapBasis hA hB : Matrix ι ι ℝ).transpose := by
  conv_lhs => rw [real_spectral hB]
  rw [overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

lemma overlap_row_weight {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hBA : B ≤ A) (i : ι) :
    ∑ j, (overlapBasis hA hB i j) ^ 2 * hB.eigenvalues j ≤ hA.eigenvalues i := by
  have h := Gain.congruence_mono hBA (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, diagonalize hA, overlap_conjugate hA hB] at h
  have hd := diag_le h i
  simpa only [sandwich_diagonal_apply, diagonal_apply_eq] using hd

lemma overlap_inverse_conjugate {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A⁻¹ * hB.eigenvectorUnitary =
      (overlapBasis hA.1 hB : Matrix ι ι ℝ).transpose *
        diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * overlapBasis hA.1 hB := by
  rw [inverse_spectral hA, overlapBasis_coe, Matrix.transpose_mul, Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

lemma diagonalize_inverse {A : Matrix ι ι ℝ} (hA : A.PosDef) :
    (hA.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose * A⁻¹ * hA.1.eigenvectorUnitary =
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) := by
  rw [inverse_spectral hA]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  rw [Matrix.mul_assoc, unitary_transpose_mul, Matrix.mul_one]

lemma overlap_col_inverse_weight {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (j : ι) :
    ∑ i, (overlapBasis hA.1 hB.1 i j) ^ 2 / hA.1.eigenvalues i ≤
      (hB.1.eigenvalues j)⁻¹ := by
  have h := Gain.congruence_mono (MatrixEnergy.inv_le_inv hB hA hBA)
    (hB.1.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, diagonalize_inverse hB,
    overlap_inverse_conjugate hA hB.1] at h
  have hd := diag_le h j
  have he := sandwich_diagonal_apply (overlapBasis hA.1 hB.1 : Matrix ι ι ℝ).transpose
    (fun i => (hA.1.eigenvalues i)⁻¹) j
  simp only [Matrix.transpose_transpose, transpose_apply] at he
  rw [he, diagonal_apply_eq] at hd
  simpa only [div_eq_mul_inv] using hd

lemma overlap_ratio_row {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (i : ι) :
    ∑ j, (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i ≤ 1 := by
  rw [← Finset.sum_div, div_le_one (hA.eigenvalues_pos i)]
  exact overlap_row_weight hA.1 hB.1 hBA i

lemma overlap_ratio_col {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) (j : ι) :
    ∑ i, (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i ≤ 1 := by
  have h := mul_le_mul_of_nonneg_right (overlap_col_inverse_weight hA hB hBA j)
    (hB.eigenvalues_pos j).le
  rw [inv_mul_cancel₀ (ne_of_gt (hB.eigenvalues_pos j)), Finset.sum_mul] at h
  calc
    _ = ∑ i, ((overlapBasis hA.1 hB.1 i j) ^ 2 / hA.1.eigenvalues i) *
        hB.1.eigenvalues j := by
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_right_comm _ _ _
    _ ≤ 1 := h

lemma trace_cfc_mul_diag {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (B : Matrix ι ι ℝ) (f : ℝ → ℝ) :
    (cfc f A * B).trace = ∑ i, f (hA.eigenvalues i) *
      ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B * hA.eigenvectorUnitary) i i := by
  rw [real_cfc hA f]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) *
        ((hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * B *
          hA.eigenvectorUnitary)).trace := by
      simp only [Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.trace, Matrix.diag, diagonal_mul]

lemma gain_new_coordinates {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) :
    (cfc (fun x => cutoff x ^ 2) A * (A - B)).trace =
      ∑ i, hA.1.eigenvalues i *
        (1 - ∑ j, (overlapBasis hA.1 hB i j) ^ 2 * hB.eigenvalues j /
          hA.1.eigenvalues i) * cutoff (hA.1.eigenvalues i) ^ 2 := by
  rw [trace_cfc_mul_diag hA.1]
  simp only [Matrix.mul_sub, Matrix.sub_mul, diagonalize hA.1,
    overlap_conjugate hA.1 hB, Matrix.sub_apply, diagonal_apply_eq,
    sandwich_diagonal_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_div]
  field_simp [ne_of_gt (hA.eigenvalues_pos i)]

lemma gain_endpoint {A B : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hBA : B ≤ A) :
    ((cfc cutoff A - cfc cutoff B) * cfc (fun (x : ℝ) => 1 + x) B *
        (cfc cutoff A - cfc cutoff B).transpose).trace +
      (cfc (fun x => cutoff x ^ 2) A * (A - B)).trace ≤
      115200 * ((cfc potential A).trace - (cfc potential B).trace) := by
  rw [weighted_cfc_distance hA.1 hB.1, gain_new_coordinates hA hB.1,
    trace_cfc hA.1, trace_cfc hB.1]
  exact gain_spectral_bound hA.1.eigenvalues hB.1.eigenvalues
    (fun i j => (overlapBasis hA.1 hB.1 i j) ^ 2)
    (fun i j => (overlapBasis hA.1 hB.1 i j) ^ 2 * hB.1.eigenvalues j /
      hA.1.eigenvalues i)
    hA.eigenvalues_pos hB.eigenvalues_pos (fun i j => sq_nonneg _)
    (sum_row_squares _) (sum_col_squares _) (fun _ _ => rfl)
    (overlap_ratio_row hA hB hBA) (overlap_ratio_col hA hB hBA)

end EuclideanSteinitz.Endpoint

namespace EuclideanSteinitz.Endpoint
open Matrix MatrixEnergy Spectral
open scoped MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma transport_row_matrix {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) :
    transportBasis hA hB C * (transportBasis hA hB C).transpose =
      (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (C * C.transpose) *
        hA.eigenvectorUnitary := by
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_mul_transpose, Matrix.mul_one]

lemma transport_col_matrix {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) :
    (transportBasis hA hB C).transpose * transportBasis hA hB C =
      (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose * (C.transpose * C) *
        hB.eigenvectorUnitary := by
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_mul_transpose, Matrix.mul_one]

lemma transport_row_bound {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C * C.transpose ≤ 1) (i : ι) :
    ∑ j, transportBasis hA hB C i j ^ 2 ≤ 1 := by
  have h := Gain.congruence_mono hC (hA.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, Matrix.mul_one, unitary_transpose_mul,
    ← transport_row_matrix hA hB C] at h
  have hd := diag_le h i
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hd

lemma transport_col_bound {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (hC : C * C.transpose ≤ 1) (j : ι) :
    ∑ i, transportBasis hA hB C i j ^ 2 ≤ 1 := by
  have h := Gain.congruence_mono (transpose_contraction hC)
    (hB.eigenvectorUnitary : Matrix ι ι ℝ).transpose
  simp only [Matrix.transpose_transpose, Matrix.mul_one, unitary_transpose_mul,
    ← transport_col_matrix hA hB C] at h
  have hd := diag_le h j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, sq] using hd

lemma transport_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) :
    transportBasis hA hB C * diagonal hB.eigenvalues * (transportBasis hA hB C).transpose =
      diagonal hA.eigenvalues := by
  rw [← diagonalize hA]
  conv_rhs => arg 1; arg 2; rw [heq, real_spectral hB]
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma transport_row_weight {A B C : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) (i : ι) :
    ∑ j, transportBasis hA hB C i j ^ 2 * hB.eigenvalues j = hA.eigenvalues i := by
  have h := congr_fun (congr_fun (transport_spectral hA hB heq) i) i
  simpa only [sandwich_diagonal_apply, diagonal_apply_eq] using h

lemma congruence_inverse {A B C : Matrix ι ι ℝ}
    (hC : IsUnit C) (heq : A = C * B * C.transpose) :
    C.transpose * A⁻¹ * C = B⁻¹ := by
  have hd := (Matrix.isUnit_iff_isUnit_det C).mp hC
  have ht := Matrix.isUnit_det_transpose C hd
  rw [heq, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ ht, Matrix.one_mul]
  rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.mul_one]

lemma transport_inverse_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) :
    (transportBasis hA.1 hB.1 C).transpose *
      diagonal (fun i => (hA.1.eigenvalues i)⁻¹) * transportBasis hA.1 hB.1 C =
        diagonal (fun i => (hB.1.eigenvalues i)⁻¹) := by
  rw [← diagonalize_inverse hB, ← congruence_inverse hC heq, inverse_spectral hA]
  simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]

lemma transport_col_inverse_weight {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) (j : ι) :
    ∑ i, transportBasis hA.1 hB.1 C i j ^ 2 / hA.1.eigenvalues i =
      (hB.1.eigenvalues j)⁻¹ := by
  have h := congr_fun (congr_fun (transport_inverse_spectral hA hB hC heq) j) j
  have hh := sandwich_diagonal_apply (transportBasis hA.1 hB.1 C).transpose
    (fun i => (hA.1.eigenvalues i)⁻¹) j
  simp only [Matrix.transpose_transpose, Matrix.transpose_apply] at hh
  rw [hh, diagonal_apply_eq] at h
  simpa only [div_eq_mul_inv] using h

lemma transport_ratio_row {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.IsHermitian) (heq : A = C * B * C.transpose) (i : ι) :
    ∑ j, transportBasis hA.1 hB C i j ^ 2 * hB.eigenvalues j / hA.1.eigenvalues i = 1 := by
  rw [← Finset.sum_div, transport_row_weight hA.1 hB heq,
    div_self (ne_of_gt (hA.eigenvalues_pos i))]

lemma transport_ratio_col {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C)
    (heq : A = C * B * C.transpose) (j : ι) :
    ∑ i, transportBasis hA.1 hB.1 C i j ^ 2 * hB.1.eigenvalues j / hA.1.eigenvalues i = 1 := by
  calc
    _ = (∑ i, transportBasis hA.1 hB.1 C i j ^ 2 / hA.1.eigenvalues i) *
        hB.1.eigenvalues j := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      exact mul_div_right_comm _ _ _
    _ = 1 := by rw [transport_col_inverse_weight hA hB hC heq,
      inv_mul_cancel₀ (ne_of_gt (hB.eigenvalues_pos j))]

lemma trace_cfc_transport_product {A B : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (C : Matrix ι ι ℝ) (f g : ℝ → ℝ) :
    (cfc f A * C * cfc g B * C.transpose).trace = ∑ i, ∑ j,
      transportBasis hA hB C i j ^ 2 * f (hA.eigenvalues i) * g (hB.eigenvalues j) := by
  rw [real_cfc hA f, real_cfc hB g]
  calc
    _ = (diagonal (fun i => f (hA.eigenvalues i)) * transportBasis hA hB C *
        diagonal (fun j => g (hB.eigenvalues j)) * (transportBasis hA hB C).transpose).trace := by
      simp only [transportBasis, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      rw [trace_mul_comm (hA.eigenvectorUnitary : Matrix ι ι ℝ)]
      simp only [Matrix.mul_assoc]
    _ = _ := by
      rw [trace_diagonal_product]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

omit [DecidableEq ι] in
lemma contraction_distance_identity {κ : Type*} [Fintype κ]
    (x : ι → ℝ) (y : κ → ℝ) (m : ι → κ → ℝ) (f : ι → ℝ) (g : κ → ℝ)
    (hrow : ∀ i, ∑ j, m i j * y j = x i) :
    (∑ i, (1 + x i) * f i ^ 2) + (∑ j, (1 + y j) * g j ^ 2) -
      2 * (∑ i, ∑ j, m i j * (1 + y j) * f i * g j) =
    (∑ i, ∑ j, m i j * (1 + y j) * (f i - g j) ^ 2) +
      (∑ i, (1 - ∑ j, m i j) * f i ^ 2) +
      (∑ j, (1 - ∑ i, m i j) * (1 + y j) * g j ^ 2) := by
  have h1 : (∑ i, ∑ j, m i j * (1 + y j) * f i ^ 2) =
      (∑ i, (1 + x i) * f i ^ 2) - (∑ i, (1 - ∑ j, m i j) * f i ^ 2) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_mul]
    simp only [mul_add, mul_one, Finset.sum_add_distrib, hrow]
    ring
  have h2 : (∑ i, ∑ j, m i j * (1 + y j) * g j ^ 2) =
      (∑ j, (1 + y j) * g j ^ 2) -
        (∑ j, (1 - ∑ i, m i j) * (1 + y j) * g j ^ 2) := by
    rw [Finset.sum_comm, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    ring
  have hexpand (i : ι) (j : κ) : m i j * (1 + y j) * (f i - g j) ^ 2 =
      m i j * (1 + y j) * f i ^ 2 + m i j * (1 + y j) * g j ^ 2 -
        2 * (m i j * (1 + y j) * f i * g j) := by ring
  simp_rw [hexpand, Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [h1, h2]
  ring

lemma contraction_endpoint_spectral {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (heq : A = C * B * C.transpose) :
    (cfc (fun x => (1 + x) * cutoff x ^ 2) A).trace +
      (cfc (fun x => (1 + x) * cutoff x ^ 2) B).trace -
      2 * (cfc cutoff A * C * cfc (fun x => (1 + x) * cutoff x) B * C.transpose).trace ≤
      115200 * ((cfc potential B).trace - (cfc potential A).trace) := by
  rw [trace_cfc hA.1, trace_cfc hB.1, trace_cfc_transport_product hA.1 hB.1,
    trace_cfc hA.1, trace_cfc hB.1]
  have hx : (∑ i, ∑ j, transportBasis hA.1 hB.1 C i j ^ 2 * cutoff (hA.1.eigenvalues i) *
      ((1 + hB.1.eigenvalues j) * cutoff (hB.1.eigenvalues j))) =
      ∑ i, ∑ j, transportBasis hA.1 hB.1 C i j ^ 2 * (1 + hB.1.eigenvalues j) *
        cutoff (hA.1.eigenvalues i) * cutoff (hB.1.eigenvalues j) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hx, contraction_distance_identity _ _ _ _ _ (transport_row_weight hA.1 hB.1 heq)]
  exact contraction_spectral_bound hA.1.eigenvalues hB.1.eigenvalues
    (fun i j => transportBasis hA.1 hB.1 C i j ^ 2)
    (fun i j => transportBasis hA.1 hB.1 C i j ^ 2 * hB.1.eigenvalues j / hA.1.eigenvalues i)
    hA.eigenvalues_pos hB.eigenvalues_pos (fun _ _ => sq_nonneg _)
    (transport_row_bound hA.1 hB.1 hContract) (transport_col_bound hA.1 hB.1 hContract)
    (fun _ _ => rfl) (transport_ratio_row hA hB.1 heq) (transport_ratio_col hA hB hC heq)

end EuclideanSteinitz.Endpoint

namespace EuclideanSteinitz.Coefficient
open Matrix MatrixEnergy Spectral Endpoint
open scoped MatrixOrder
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_nonneg (D : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.PosSemidef) :
    0 ≤ weightedSq D W := by
  have h : (D * W * D.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hW.mul_mul_conjTranspose_same D
  exact h.trace_nonneg

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_weight_add (D : Matrix ι κ ℝ) (W V : Matrix κ κ ℝ) :
    weightedSq D (W + V) = weightedSq D W + weightedSq D V := by
  simp only [weightedSq, Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weighted_cross_symm (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.transpose = W) :
    (D * W * E.transpose).trace = (E * W * D.transpose).trace := by
  rw [← Matrix.trace_transpose (D * W * E.transpose)]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, hW, Matrix.mul_assoc]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_sub (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.transpose = W) :
    weightedSq (D - E) W = weightedSq D W + weightedSq E W -
      2 * (D * W * E.transpose).trace := by
  simp only [weightedSq, Matrix.transpose_sub, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [weighted_cross_symm E D hW]
  ring

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_triangle (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ} (hW : W.PosSemidef) :
    weightedSq (D + E) W ≤ 2 * weightedSq D W + 2 * weightedSq E W := by
  have hn := weightedSq_nonneg (D - E) hW
  have hi : weightedSq (D + E) W + weightedSq (D - E) W =
      2 * weightedSq D W + 2 * weightedSq E W := by
    simp only [weightedSq, Matrix.transpose_add, Matrix.transpose_sub, Matrix.add_mul,
      Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.trace_add, Matrix.trace_sub]
    ring
  linarith only [hn, hi]

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma lift_sub (R : Matrix ι κ ℝ) (A B : Matrix ι ι ℝ) :
    lift R (A - B) = lift R A - lift R B := by
  simp only [lift, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] [DecidableEq κ] in
lemma weighted_lift_cross (R S : Matrix ι κ ℝ) (A B : Matrix ι ι ℝ)
    (W : Matrix κ κ ℝ) :
    (lift R A * W * (lift S B).transpose).trace =
      (A * (R * W * S.transpose) * B.transpose * (S * R.transpose)).trace := by
  simp only [lift, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
  rw [Matrix.trace_mul_comm R.transpose]
  simp only [Matrix.mul_assoc]

omit [DecidableEq κ] in
lemma weighted_lift (R : Matrix ι κ ℝ) (hR : R * R.transpose = 1)
    (A : Matrix ι ι ℝ) (W : Matrix κ κ ℝ) :
    weightedSq (lift R A) W = weightedSq A (R * W * R.transpose) := by
  unfold weightedSq
  rw [weighted_lift_cross, hR, Matrix.mul_one]

lemma cfc_transpose {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).transpose = cfc f A := by
  rw [real_cfc hA f]
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
    Matrix.mul_assoc]

lemma cfc_square {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    cfc f A * cfc f A = cfc (fun x => f x ^ 2) A := by
  rw [real_cfc hA f, real_cfc hA (fun x => f x ^ 2)]
  simp only [Matrix.mul_assoc]
  simp only [← Matrix.mul_assoc, unitary_transpose_mul, Matrix.one_mul]
  congr 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.diagonal_mul_diagonal]
  simp only [sq]

lemma cfc_affine {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    cfc (fun x : ℝ => 1 + x) A = 1 + A := by
  rw [cfc_add A (fun _ : ℝ => 1) (fun x : ℝ => x) continuousOn_const continuousOn_id,
    cfc_const_one ℝ A, cfc_id' ℝ A hA.isSelfAdjoint]

lemma weightedSq_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (f : ℝ → ℝ) (W : Matrix ι ι ℝ) :
    weightedSq (cfc f A) W = (cfc (fun x => f x ^ 2) A * W).trace := by
  unfold weightedSq
  rw [cfc_transpose hA f, Matrix.trace_mul_cycle, cfc_square hA]

lemma cfc_mul_same {A : Matrix ι ι ℝ} (_hA : A.IsHermitian) (f g : ℝ → ℝ) :
    cfc f A * cfc g A = cfc (fun x => f x * g x) A := by
  have hf : ContinuousOn f (spectrum ℝ A) := Gain.finite_spectrum_continuous _ _
  have hg : ContinuousOn g (spectrum ℝ A) := Gain.finite_spectrum_continuous _ _
  exact (cfc_mul f g A hf hg).symm

lemma weightedSq_cfc_affine {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    weightedSq (cfc f A) (1 + A) = (cfc (fun x => (1 + x) * f x ^ 2) A).trace := by
  rw [weightedSq_cfc hA, ← cfc_affine hA, cfc_mul_same hA]
  congr 2
  funext x
  exact mul_comm _ _

omit [DecidableEq κ] in
lemma contraction_endpoint {A B C : Matrix ι ι ℝ}
    (hA : A.PosDef) (hB : B.PosDef) (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (heq : A = C * B * C.transpose)
    (R S : Matrix ι κ ℝ) (hR : R * R.transpose = 1) (hS : S * S.transpose = 1)
    (W : Matrix κ κ ℝ) (hW : W.transpose = W)
    (hRW : R * W * R.transpose = 1 + A) (hSW : S * W * S.transpose = 1 + B)
    (hRS : R * S.transpose = C) (hRWS : R * W * S.transpose = C * (1 + B)) :
    weightedSq (lift R (cfc cutoff A) - lift S (cfc cutoff B)) W ≤
      115200 * ((cfc potential B).trace - (cfc potential A).trace) := by
  have hSR : S * R.transpose = C.transpose := by
    rw [← hRS, Matrix.transpose_mul, Matrix.transpose_transpose]
  have haff : (1 + B) * cfc cutoff B = cfc (fun x => (1 + x) * cutoff x) B := by
    rw [← cfc_affine hB.1, cfc_mul_same hB.1]
  have hcross : (lift R (cfc cutoff A) * W * (lift S (cfc cutoff B)).transpose).trace =
      (cfc cutoff A * C * cfc (fun x => (1 + x) * cutoff x) B * C.transpose).trace := by
    rw [weighted_lift_cross, hRWS, cfc_transpose hB.1, hSR, ← haff]
    simp only [Matrix.mul_assoc]
  rw [weightedSq_sub _ _ hW, weighted_lift R hR, weighted_lift S hS, hRW, hSW,
    weightedSq_cfc_affine hA.1, weightedSq_cfc_affine hB.1, hcross]
  exact contraction_endpoint_spectral hA hB hC hContract heq

omit [DecidableEq ι] [DecidableEq κ] in
lemma weightedSq_sub_zero (D E : Matrix ι κ ℝ) {W : Matrix κ κ ℝ}
    (hW : W.transpose = W) (hEW : E * W = 0) :
    weightedSq (D - E) W = weightedSq D W := by
  rw [weightedSq_sub _ _ hW, weighted_cross_symm D E hW]
  simp only [weightedSq, hEW, Matrix.zero_mul, Matrix.trace_zero, mul_zero, add_zero, sub_zero]

lemma gain_endpoint_lift {X Z : Matrix ι ι ℝ}
    (hX : X.PosDef) (hZ : Z.PosDef) (hZX : Z ≤ X)
    (R : Matrix ι κ ℝ) (hR : R * R.transpose = 1)
    (E Qold Qnew : Matrix κ κ ℝ) (hNew : Qnew.transpose = Qnew)
    (hEq : E * Qnew = 0)
    (hOld : R * Qold * R.transpose = Z) (hNewState : R * Qnew * R.transpose = X - Z) :
    weightedSq (lift R (cfc cutoff X) - lift R (cfc cutoff Z)) (1 + Qold) +
      weightedSq (lift R (cfc cutoff X) - E) Qnew ≤
      115200 * ((cfc potential X).trace - (cfc potential Z).trace) := by
  rw [← lift_sub, weighted_lift R hR,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hR, hOld,
    weightedSq_sub_zero _ _ hNew hEq, weighted_lift R hR, hNewState,
    weightedSq_cfc hX.1, ← cfc_affine hZ.1]
  exact gain_endpoint hX hZ hZX

lemma endpoint_comparison {X Y Z C : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (hZeq : Z = C * Y * C.transpose)
    (T S : Matrix ι κ ℝ) (hT : T * T.transpose = 1) (hS : S * S.transpose = 1)
    (Qold Qnew : Matrix κ κ ℝ) (hOldPSD : Qold.PosSemidef) (hNewPSD : Qnew.PosSemidef)
    (hOldS : S * Qold * S.transpose = Y) (hOldT : T * Qold * T.transpose = Z)
    (hTS : T * S.transpose = C) (hCross : T * Qold * S.transpose = C * Y)
    (hNewT : T * Qnew * T.transpose = X - Z)
    (hZero : lift S (cfc cutoff Y) * Qnew = 0) :
    weightedSq (lift T (cfc cutoff X) - lift S (cfc cutoff Y)) ((1 + Qold) + Qnew) ≤
      230400 * (((cfc potential Y).trace - (cfc potential Z).trace) +
        ((cfc potential X).trace - (cfc potential Z).trace)) := by
  let F1 := lift T (cfc cutoff X)
  let Fm := lift T (cfc cutoff Z)
  let F0 := lift S (cfc cutoff Y)
  let W := (1 : Matrix κ κ ℝ) + Qold
  have hWPSD : W.PosSemidef := Matrix.PosSemidef.one.add hOldPSD
  have hWsymm : W.transpose = W := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hWPSD.1
  have hNewSymm : Qnew.transpose = Qnew := by
    simpa only [Matrix.IsHermitian, conjTranspose_eq_transpose_of_trivial] using hNewPSD.1
  have hTW : T * W * T.transpose = 1 + Z := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hT, hOldT]
  have hSW : S * W * S.transpose = 1 + Y := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hS, hOldS]
  have hTWS : T * W * S.transpose = C * (1 + Y) := by
    simp only [W, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hTS, hCross]
  have hZX : Z ≤ X := by
    apply Matrix.le_iff.mpr
    rw [← hNewT]
    simpa only [conjTranspose_eq_transpose_of_trivial] using hNewPSD.mul_mul_conjTranspose_same T
  have hcontr := contraction_endpoint hZ hY hC hContract hZeq T S hT hS W hWsymm
    hTW hSW hTS hTWS
  change weightedSq (Fm - F0) W ≤ _ at hcontr
  have hgain := gain_endpoint_lift hX hZ hZX T hT F0 Qold Qnew hNewSymm hZero hOldT hNewT
  change weightedSq (F1 - Fm) W + weightedSq (F1 - F0) Qnew ≤ _ at hgain
  have hpos := weightedSq_nonneg (F1 - F0) hNewPSD
  have htri : weightedSq (F1 - F0) W ≤
      2 * weightedSq (F1 - Fm) W + 2 * weightedSq (Fm - F0) W := by
    have heq : F1 - F0 = (F1 - Fm) + (Fm - F0) := by abel
    conv_lhs => rw [heq]
    exact weightedSq_triangle _ _ hWPSD
  change weightedSq (F1 - F0) (W + Qnew) ≤ _
  rw [weightedSq_weight_add]
  linarith only [htri, hgain, hcontr, hpos]

end EuclideanSteinitz.Coefficient

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Energy
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Telescoping matrix energy and trace budgets. -/

namespace EuclideanSteinitz.Energy
open Matrix MatrixEnergy Gain Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma pTrace_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hAB : A ≤ B) : pTrace A ≤ pTrace B := by
  dsimp only [pTrace]
  rw [← cfc_primitive_eq hA, ← cfc_primitive_eq hB]
  exact trace_primitive_monotone hA.1 hB.1 hAB

lemma gainValue_mono {A B : Matrix ι ι ℝ} (hA : A.PosSemidef) (hAB : A ≤ B) :
    gainValue A ≤ gainValue B := by
  have h := gainValue_monotone hA (Matrix.le_iff.mp hAB)
    (show (0 : ℝ) ≤ 0 by rfl) (show (0 : ℝ) ≤ 1 by norm_num) (show (0 : ℝ) ≤ 1 by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel] using h

lemma trace_contraction {f : ℝ → ℝ}
    (hf : ∀ {A B : Matrix ι ι ℝ}, A.PosSemidef → B.PosSemidef → A ≤ B →
      (cfc f A).trace ≤ (cfc f B).trace)
    {A C : Matrix ι ι ℝ} (hA : A.PosSemidef) (hC : C * C.transpose ≤ 1) :
    (cfc f (C * A * C.transpose)).trace ≤ (cfc f A).trace := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [trace_cfc_eq_of_charpoly hCA.1 hSC.1 heq]
  exact hf hSC hA hle

lemma pTrace_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) : pTrace (C * A * C.transpose) ≤ pTrace A :=
  trace_contraction (fun hA hB hAB => pTrace_mono hA hB hAB) hA hC

lemma gainValue_contraction {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) : gainValue (C * A * C.transpose) ≤ gainValue A :=
  trace_contraction (fun hA _ hAB => gainValue_mono hA hAB) hA hC

lemma Move.old_le_next {p : Move ι} (hp : p.Admissible) (D : Matrix ι ι ℝ) :
    p.old D ≤ p.next D := by
  exact le_add_of_nonneg_right hp.2.nonneg

lemma step_bounds {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {p : Move ι}
    (hp : p.Admissible) :
    0 ≤ pTrace D - pTrace (p.old D) ∧
    0 ≤ gainValue D - gainValue (p.old D) ∧
    0 ≤ pTrace (p.next D) - pTrace (p.old D) ∧
    0 ≤ gainValue (p.next D) - gainValue (p.old D) := by
  exact ⟨sub_nonneg.mpr (pTrace_contraction hD hp.1),
    sub_nonneg.mpr (gainValue_contraction hD hp.1),
    sub_nonneg.mpr (pTrace_mono (p.old_psd hD) (p.next_psd hp hD) (Move.old_le_next hp D)),
    p.gain_nonneg hp hD⟩

lemma stepCost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {p : Move ι}
    (hp : p.Admissible) : 0 ≤ stepCost p D := by
  obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp
  dsimp only [stepCost, hTrace]
  linarith

lemma cost_nonneg {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : 0 ≤ cost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    exact add_nonneg (stepCost_nonneg hD hp₀)
      (ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq)))

lemma gainCost_le_cost {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : gainCost D ps ≤ cost D ps := by
  induction ps generalizing D with
  | nil => rfl
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have hi := ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp₀
    dsimp only [gainCost, cost, stepCost, hTrace]
    linarith

lemma trace_change_le_cost {D : Matrix ι ι ℝ} (hD : D.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) : pTrace D - pTrace (finish D ps) ≤ cost D ps := by
  induction ps generalizing D with
  | nil => simp only [finish, cost, sub_self, le_refl]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have hi := ih (p.next_psd hp₀ hD) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    obtain ⟨h₁,h₂,h₃,h₄⟩ := step_bounds hD hp₀
    dsimp only [finish, cost, stepCost, hTrace]
    linarith

omit [DecidableEq ι] in
lemma finish_eq_follow (Z V : Matrix ι ι ℝ) (ps : List (Move ι)) :
    finish (Z + V) ps = (follow Z V ps).1 + (follow Z V ps).2 := by
  induction ps generalizing Z V with
  | nil => rfl
  | cons p ps ih =>
    simp only [finish, follow]
    rw [show p.next (Z + V) = p.old Z + p.next V by simp [Move.next, p.old_add, add_assoc]]
    exact ih _ _

omit [DecidableEq ι] in
lemma finish_eq_follow_zero (Y : Matrix ι ι ℝ) (ps : List (Move ι)) :
    finish Y ps = (follow Y 0 ps).1 + (follow Y 0 ps).2 := by
  simpa only [add_zero] using finish_eq_follow Y 0 ps

lemma endpoint_cost {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ} (hcost : cost Y ps ≤ E)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let Z := (follow Y 0 ps).1
    let X := finish Y ps
    (pTrace Y - pTrace Z) + (pTrace X - pTrace Z) ≤
      E + 16 * (gainConstant * E) ^ (1 / exponent) * (cfc sizeWeight X).trace := by
  dsimp only
  have hbound := accumulated_gain_bound hY hp ((gainCost_le_cost hY hp).trans hcost) hsmall
  obtain ⟨hq, hq₁, _, hb⟩ := hbound
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hX : (finish Y ps).PosSemidef := by
    rw [finish_eq_follow_zero]
    exact hpsd.1.add hpsd.2
  have hXZ : finish Y ps - (follow Y 0 ps).1 ≤
      (gainConstant * E) ^ (1 / exponent) • (1 + finish Y ps) := by
    rw [finish_eq_follow_zero, add_sub_cancel_left]
    exact hb
  have hg := trace_potential_direct hX hpsd.1 hq hq₁.le hXZ
  have ht := (trace_change_le_cost hY hp).trans hcost
  change pTrace (finish Y ps) - pTrace (follow Y 0 ps).1 ≤ _ at hg
  linarith

lemma gainConstant_one_le : 1 ≤ gainConstant := by
  have hs : 1 ≤ Real.sqrt 8 := by
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [gainConstant, two_rpow_exponent]
  norm_num [exponent]
  nlinarith

lemma sizeTrace_nonneg {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    0 ≤ (cfc sizeWeight X).trace := by
  apply Matrix.PosSemidef.trace_nonneg
  apply Matrix.nonneg_iff_posSemidef.mp
  apply cfc_nonneg
  intro x hx
  have hx₀ := spectrum_nonneg_of_nonneg hX.nonneg hx
  exact le_min (Real.rpow_nonneg hx₀ _) (inv_nonneg.mpr hx₀)

lemma incrementConstant_pos : 0 < incrementConstant := by
  have hc := gainConstant_pos
  unfold incrementConstant
  positivity

lemma cost_power_bound {E k : ℝ} (hE : 0 ≤ E) (hk : 0 ≤ k)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    E + 16 * (gainConstant * E) ^ (1 / exponent) * k ≤
      (1 + 16 * gainConstant ^ (1 / exponent)) * (1 + k) * E ^ (1 / exponent) := by
  have hc := gainConstant_one_le
  have hE1 : E ≤ 1 := by
    have hh := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) gainConstant_pos)).mp hsmall
    nlinarith
  have he := Real.self_le_rpow_of_le_one hE hE1 (show 1 / exponent ≤ 1 by norm_num [exponent])
  have hr : 0 ≤ E ^ (1 / exponent) := Real.rpow_nonneg hE _
  have hc₀ : 0 ≤ gainConstant ^ (1 / exponent) := Real.rpow_nonneg gainConstant_pos.le _
  rw [Real.mul_rpow gainConstant_pos.le hE]
  nlinarith [mul_nonneg (mul_nonneg hc₀ hr) (by norm_num : (0 : ℝ) ≤ 16), mul_nonneg hk hr]

lemma endpoint_cost_power {Y : Matrix ι ι ℝ} (hY : Y.PosSemidef) {ps : List (Move ι)}
    (hp : ∀ p ∈ ps, p.Admissible) {E : ℝ} (hcost : cost Y ps ≤ E)
    (hsmall : E ≤ 1 / (16 * gainConstant)) :
    let Z := (follow Y 0 ps).1
    let X := finish Y ps
    (pTrace Y - pTrace Z) + (pTrace X - pTrace Z) ≤
      (1 + 16 * gainConstant ^ (1 / exponent)) * (1 + (cfc sizeWeight X).trace) *
        E ^ (1 / exponent) := by
  dsimp only
  have hpsd := follow_psd hY Matrix.PosSemidef.zero hp
  have hX : (finish Y ps).PosSemidef := by
    rw [finish_eq_follow_zero]
    exact hpsd.1.add hpsd.2
  exact (endpoint_cost hY hp hcost hsmall).trans
    (cost_power_bound ((cost_nonneg hY hp).trans hcost) (sizeTrace_nonneg hX) hsmall)

end EuclideanSteinitz.Energy

namespace EuclideanSteinitz.Coefficient
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma weighted_increment {X Y Z C : Matrix ι ι ℝ}
    (hX : X.PosDef) (hY : Y.PosDef) (hZ : Z.PosDef)
    (hC : IsUnit C) (hContract : C * C.transpose ≤ 1)
    (hZeq : Z = C * Y * C.transpose)
    (T S : Matrix ι κ ℝ) (hT : T * T.transpose = 1) (hS : S * S.transpose = 1)
    (Qold Qnew : Matrix κ κ ℝ) (hOldPSD : Qold.PosSemidef) (hNewPSD : Qnew.PosSemidef)
    (hOldS : S * Qold * S.transpose = Y) (hOldT : T * Qold * T.transpose = Z)
    (hTS : T * S.transpose = C) (hCross : T * Qold * S.transpose = C * Y)
    (hNewT : T * Qnew * T.transpose = X - Z)
    (hZero : lift S (cfc cutoff Y) * Qnew = 0)
    (ps : List (Move ι)) (hp : ∀ p ∈ ps, p.Admissible)
    (hEndX : X = finish Y ps) (hEndZ : Z = (follow Y 0 ps).1)
    {E : ℝ} (hCost : cost Y ps ≤ E) (hSmall : E ≤ 1 / (16 * gainConstant)) :
    weightedSq (lift T (cfc cutoff X) - lift S (cfc cutoff Y)) ((1 + Qold) + Qnew) ≤
      incrementConstant * (1 + (cfc sizeWeight X).trace) * E ^ (1 / exponent) := by
  have h₁ := endpoint_comparison hX hY hZ hC hContract hZeq T S hT hS Qold Qnew
    hOldPSD hNewPSD hOldS hOldT hTS hCross hNewT hZero
  have h₂ := endpoint_cost_power hY.posSemidef hp hCost hSmall
  dsimp only at h₂
  rw [← hEndX, ← hEndZ] at h₂
  have h₃ := mul_le_mul_of_nonneg_left h₂ (by norm_num : (0 : ℝ) ≤ 230400)
  dsimp only [pTrace] at h₃
  unfold incrementConstant
  calc
    _ ≤ _ := h₁.trans h₃
    _ = _ := by ring

end EuclideanSteinitz.Coefficient

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Filter
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Symmetric contraction updates and filtered matrix states. -/

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma mul_insert_transpose (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ) :
    R * (insert b j).transpose = vecMulVec (fun i => R i j) b := by
  ext i k
  simp [Matrix.mul_apply, insert, Matrix.transpose_apply, vecMulVec_apply]

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_transpose_zero (R : Matrix ι κ ℝ) (b : ι → ℝ) (j : κ)
    (hR : ∀ i, R i j = 0) : insert b j * R.transpose = 0 := by
  apply Matrix.transpose_injective
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero,
    mul_insert_transpose]
  ext i k
  simp only [vecMulVec_apply, hR, zero_mul, Matrix.zero_apply]

omit [Fintype κ] [DecidableEq ι] in
lemma step_apply_column (p : Step ι κ) (R : Matrix ι κ ℝ) {j : κ}
    (hj : j ≠ p.j) (hR : ∀ i, R i j = 0) : ∀ i, p.apply R i j = 0 := by
  intro i
  simp [Step.apply, Matrix.mul_apply, insert, hj, hR]

lemma Step.coisometry {p : Step ι κ} (hp : p.Good) {R : Matrix ι κ ℝ}
    (hR : R * R.transpose = 1) (hf : ∀ i, R i p.j = 0) :
    p.apply R * (p.apply R).transpose = 1 := by
  have hz : R * (insert p.b p.j).transpose = 0 := by
    rw [mul_insert_transpose]
    ext i k
    simp [vecMulVec_apply, hf]
  have hz' := insert_mul_transpose_zero R p.b p.j hf
  have h₁ : p.C * R * (p.C * R).transpose = p.C * p.C.transpose := by
    rw [Matrix.transpose_mul, Matrix.mul_assoc p.C R, ← Matrix.mul_assoc R, hR, Matrix.one_mul]
  have h₂ : p.C * R * (insert p.b p.j).transpose = 0 := by
    rw [Matrix.mul_assoc, hz, Matrix.mul_zero]
  have h₃ : insert p.b p.j * (p.C * R).transpose = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hz', Matrix.zero_mul]
  simpa only [Step.apply, Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    h₁, h₂, h₃, insert_mul_transpose, add_zero, zero_add] using hp.2

omit [Fintype κ] [DecidableEq κ] in
lemma Step.admissible {p : Step ι κ} (hp : p.Good) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) :
    (p.move q).Admissible :=
  ⟨Step.contract hp, (rankOne_psd p.b).smul (hq p.j)⟩

omit [Fintype κ] [DecidableEq ι] in
lemma Step.fresh_tail {p : Step ι κ} {ps : List (Step ι κ)} {R : Matrix ι κ ℝ}
    (hf : Fresh R (p :: ps)) (hd : ∀ r ∈ ps, p.j ≠ r.j) : Fresh (p.apply R) ps := by
  intro r hr
  exact step_apply_column p R (Ne.symm (hd r hr)) (hf r (List.mem_cons_of_mem p hr))

lemma run_coisometry {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) (hf : Fresh R ps)
    (hd : (ps.map Step.j).Nodup) : run R ps * (run R ps).transpose = 1 := by
  induction ps generalizing R with
  | nil => exact hR
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r ∈ ps, p.j ≠ r.j := by
      intro r hr he
      apply hd'.1
      exact List.mem_map.mpr ⟨r, hr, he.symm⟩
    exact ih (Step.coisometry (hp p (List.mem_cons_self ..)) hR (hf p (List.mem_cons_self ..)))
      (fun r hr => hp r (List.mem_cons_of_mem p hr)) (Step.fresh_tail hf htail) hd'.2

omit [Fintype κ] [DecidableEq κ] in
lemma product_contract {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) :
    product ps * (product ps).transpose ≤ 1 := by
  induction ps with
  | nil => simp [product]
  | cons p ps ih =>
    have hp₀ := Step.contract (hp p (List.mem_cons_self ..))
    have hps := ih (fun r hr => hp r (List.mem_cons_of_mem p hr))
    have hh := Gain.congruence_mono hp₀ (product ps)
    simp only [Matrix.mul_one] at hh
    have he : product (p :: ps) * (product (p :: ps)).transpose ≤
        product ps * (product ps).transpose := by
      simpa only [product, Matrix.transpose_mul, Matrix.mul_assoc] using hh
    exact he.trans hps

omit [Fintype κ] [DecidableEq κ] in
lemma product_unit {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) : IsUnit (product ps) := by
  induction ps with
  | nil => exact isUnit_one
  | cons p ps ih =>
    exact (ih (fun r hr => hp r (List.mem_cons_of_mem p hr))).mul (hp p (List.mem_cons_self ..)).1

omit [Fintype ι] [DecidableEq ι] in
lemma insert_diagonal (b : ι → ℝ) (j : κ) (q : κ → ℝ) :
    insert b j * diagonal q = q j • insert b j := by
  ext i k
  simp only [Matrix.mul_diagonal, insert, Matrix.smul_apply, smul_eq_mul]
  by_cases h : k = j
  · simp [h, mul_comm]
  · simp [h]

omit [DecidableEq ι] in
lemma Step.state_next {R : Matrix ι κ ℝ} (p : Step ι κ) (q : κ → ℝ)
    (hf : ∀ i, R i p.j = 0) : state q (p.apply R) = (p.move q).next (state q R) := by
  have hz : R * diagonal q * (insert p.b p.j).transpose = 0 := by
    rw [mul_insert_transpose]
    ext i k
    simp [vecMulVec_apply, Matrix.mul_diagonal, hf]
  have hz' : insert p.b p.j * diagonal q * R.transpose = 0 := by
    rw [insert_diagonal, Matrix.smul_mul, insert_mul_transpose_zero R p.b p.j hf, smul_zero]
  have h₁ : p.C * R * diagonal q * (p.C * R).transpose =
      p.C * state q R * p.C.transpose := by
    simp only [state, Matrix.transpose_mul, Matrix.mul_assoc]
  have h₂ : p.C * R * diagonal q * (insert p.b p.j).transpose = 0 := by
    simpa only [Matrix.mul_assoc, Matrix.mul_zero] using congrArg (fun M => p.C * M) hz
  have h₃ : insert p.b p.j * diagonal q * (p.C * R).transpose = 0 := by
    rw [Matrix.transpose_mul, ← Matrix.mul_assoc, hz', Matrix.zero_mul]
  have h₄ : insert p.b p.j * diagonal q * (insert p.b p.j).transpose =
      q p.j • vecMulVec p.b p.b := by
    rw [insert_diagonal, Matrix.smul_mul, insert_mul_transpose]
  simp only [state, Step.apply, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add,
    h₁, h₂, h₃, h₄, add_zero, zero_add]
  rfl

omit [DecidableEq ι] in
lemma run_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (q : κ → ℝ)
    (hf : Fresh R ps) (hd : (ps.map Step.j).Nodup) :
    state q (run R ps) = finish (state q R) (ps.map (fun p => p.move q)) := by
  induction ps generalizing R with
  | nil => rfl
  | cons p ps ih =>
    have hd' := List.nodup_cons.mp hd
    have htail : ∀ r ∈ ps, p.j ≠ r.j := by
      intro r hr he
      exact hd'.1 (List.mem_map.mpr ⟨r, hr, he.symm⟩)
    simp only [run, List.map_cons, finish]
    rw [ih (Step.fresh_tail hf htail) hd'.2,
      Step.state_next p q (hf p (List.mem_cons_self ..))]

omit [Fintype κ] [DecidableEq κ] in
lemma follow_old (Z V : Matrix ι ι ℝ) (ps : List (Step ι κ)) (q : κ → ℝ) :
    (follow Z V (ps.map (fun p => p.move q))).1 = product ps * Z * (product ps).transpose := by
  induction ps generalizing Z V with
  | nil => simp [follow, product]
  | cons p ps ih =>
    change (follow ((p.move q).old Z) ((p.move q).next V)
      (ps.map (fun p => p.move q))).1 = _
    rw [ih]
    simp only [product, Step.move, Move.old, Matrix.transpose_mul, Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma insert_mul_zero {μ : Type*} (b : ι → ℝ) (j : κ) (B : Matrix κ μ ℝ)
    (hz : ∀ l, B j l = 0) : insert b j * B = 0 := by
  ext i l
  simp [Matrix.mul_apply, insert, hz]

lemma run_mul {μ : Type*} (R : Matrix ι κ ℝ) (ps : List (Step ι κ)) (B : Matrix κ μ ℝ)
    (hz : ∀ p ∈ ps, ∀ l, B p.j l = 0) : run R ps * B = product ps * R * B := by
  induction ps generalizing R with
  | nil => simp [run, product]
  | cons p ps ih =>
    simp only [run]
    rw [ih _ (fun r hr => hz r (List.mem_cons_of_mem p hr))]
    simp only [Step.apply, product, Matrix.mul_add, Matrix.add_mul]
    rw [Matrix.mul_assoc (product ps) (insert p.b p.j),
      insert_mul_zero _ _ _ (hz p (List.mem_cons_self ..)), Matrix.mul_zero, add_zero]
    simp only [Matrix.mul_assoc]

omit [Fintype ι] [Fintype κ] [DecidableEq ι] in
lemma mem_newSet {p : Step ι κ} {ps : List (Step ι κ)} (hp : p ∈ ps) : p.j ∈ newSet ps := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨p, hp, rfl⟩)

lemma oldQ_eq (J : Finset κ) (q : κ → ℝ) :
    oldQ J q = oldMask J * diagonal q * (oldMask J).transpose := by
  simp only [oldQ, oldMask, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  congr 1
  funext j
  split <;> simp_all

omit [Fintype κ] in
lemma oldQ_add_newQ (J : Finset κ) (q : κ → ℝ) : oldQ J q + newQ J q = diagonal q := by
  rw [oldQ, newQ, Matrix.diagonal_add]
  congr 1
  funext j
  split <;> simp_all

omit [Fintype κ] in
lemma oldQ_psd (J : Finset κ) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) : (oldQ J q).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split <;> simp_all

omit [Fintype κ] in
lemma newQ_psd (J : Finset κ) {q : κ → ℝ} (hq : ∀ j, 0 ≤ q j) : (newQ J q).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  dsimp only
  split <;> simp_all

omit [Fintype ι] [DecidableEq ι] in
lemma oldQ_sandwich (A B : Matrix ι κ ℝ) (J : Finset κ) (q : κ → ℝ) :
    A * oldQ J q * B.transpose =
      (A * oldMask J) * diagonal q * (B * oldMask J).transpose := by
  rw [oldQ_eq, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_oldMask {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) :
    R * oldMask (newSet ps) = R := by
  ext i j
  simp only [oldMask, Matrix.mul_diagonal]
  by_cases hj : j ∈ newSet ps
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    simp only [ite_eq_left hj, mul_zero, hf p hp i]
  · simp [hj]

omit [Fintype ι] [DecidableEq ι] in
lemma fresh_newQ {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) (q : κ → ℝ) :
    R * newQ (newSet ps) q = 0 := by
  ext i j
  simp only [newQ, Matrix.mul_diagonal, Matrix.zero_apply]
  by_cases hj : j ∈ newSet ps
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    simp only [ite_eq_left hj, hf p hp i, zero_mul]
  · simp [hj]

lemma run_oldMask {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps) :
    run R ps * oldMask (newSet ps) = product ps * R := by
  rw [run_mul]
  · rw [Matrix.mul_assoc, fresh_oldMask hf]
  · intro p hp l
    simp only [oldMask, Matrix.diagonal_apply]
    by_cases h : p.j = l
    · subst l
      simp [mem_newSet hp]
    · simp [h]

lemma run_cross {R : Matrix ι κ ℝ} {ps : List (Step ι κ)} (hf : Fresh R ps)
    (hR : R * R.transpose = 1) : run R ps * R.transpose = product ps := by
  rw [run_mul R ps R.transpose (fun p hp l => hf p hp l), Matrix.mul_assoc, hR, Matrix.mul_one]

omit [Fintype ι] [DecidableEq ι] in
lemma old_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    R * oldQ (newSet ps) q * R.transpose = state q R := by
  rw [oldQ_sandwich, fresh_oldMask hf]
  rfl

lemma run_old_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * oldQ (newSet ps) q * (run R ps).transpose =
      product ps * state q R * (product ps).transpose := by
  rw [oldQ_sandwich, run_oldMask hf]
  simp only [state, Matrix.transpose_mul, Matrix.mul_assoc]

lemma run_old_cross {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * oldQ (newSet ps) q * R.transpose = product ps * state q R := by
  rw [oldQ_sandwich, run_oldMask hf, fresh_oldMask hf]
  simp only [state, Matrix.mul_assoc]

lemma run_new_state {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) :
    run R ps * newQ (newSet ps) q * (run R ps).transpose =
      state q (run R ps) - product ps * state q R * (product ps).transpose := by
  have he : run R ps * oldQ (newSet ps) q * (run R ps).transpose +
      run R ps * newQ (newSet ps) q * (run R ps).transpose = state q (run R ps) := by
    rw [← Matrix.add_mul, ← Matrix.mul_add, oldQ_add_newQ]
    rfl
  rw [run_old_state hf] at he
  exact eq_sub_of_add_eq' he

omit [DecidableEq ι] in
lemma fresh_lift_new_zero {R : Matrix ι κ ℝ} {ps : List (Step ι κ)}
    (hf : Fresh R ps) (q : κ → ℝ) (A : Matrix ι ι ℝ) :
    Coefficient.lift R A * newQ (newSet ps) q = 0 := by
  rw [Coefficient.lift, Matrix.mul_assoc, fresh_newQ hf q, Matrix.mul_zero]

lemma weighted_increment {R : Matrix ι κ ℝ} (hR : R * R.transpose = 1)
    {ps : List (Step ι κ)} (hp : ∀ p ∈ ps, p.Good) (hf : Fresh R ps)
    (hd : (ps.map Step.j).Nodup) {q : κ → ℝ} (hq : ∀ j, 0 < q j)
    {E : ℝ} (hCost : cost (state q R) (ps.map (fun p => p.move q)) ≤ E)
    (hSmall : E ≤ 1 / (16 * gainConstant)) :
    Coefficient.weightedSq
      (Coefficient.lift (run R ps) (cfc cutoff (state q (run R ps))) -
        Coefficient.lift R (cfc cutoff (state q R))) (1 + diagonal q) ≤
      incrementConstant * (1 + (cfc sizeWeight (state q (run R ps))).trace) *
        E ^ (1 / exponent) := by
  have hT := run_coisometry hR hp hf hd
  have hY := state_posDef hR hq
  have hX := state_posDef hT hq
  have hC := product_unit hp
  have hZ : (product ps * state q R * (product ps).transpose).PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hY.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hC)
  have hMoves : ∀ p ∈ ps.map (fun p => p.move q), p.Admissible := by
    intro p hp'
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hp'
    exact Step.admissible (hp r hr) (fun j => (hq j).le)
  have he := Coefficient.weighted_increment hX hY hZ hC (product_contract hp) rfl
    (run R ps) R hT hR (oldQ (newSet ps) q) (newQ (newSet ps) q)
    (oldQ_psd _ (fun j => (hq j).le)) (newQ_psd _ (fun j => (hq j).le))
    (old_state hf q) (run_old_state hf q) (run_cross hf hR) (run_old_cross hf q)
    (run_new_state hf q) (fresh_lift_new_zero hf q _) _ hMoves
    (run_state q hf hd) (follow_old _ _ _ _).symm hCost hSmall
  simpa only [add_assoc, oldQ_add_newQ] using he

end EuclideanSteinitz.Filter

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Scales
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Uniform dyadic scale-energy estimates. -/

namespace EuclideanSteinitz.Scale
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator

lemma size_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ sizeWeight x :=
  le_min (Real.rpow_nonneg hx _) (inv_nonneg.mpr hx)

lemma size_le_sqrt (x : ℝ) : sizeWeight x ≤ Real.sqrt x := by
  unfold sizeWeight
  rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
  exact min_le_left _ _

lemma size_le_inv (x : ℝ) : sizeWeight x ≤ x⁻¹ := min_le_right _ _

lemma size_dyadic_nat {y : ℝ} (_hy : 0 ≤ y) (hy2 : y ≤ 2) (n : ℕ) :
    sizeWeight (y / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ n := by
  apply (size_le_sqrt _).trans
  have hn : (1 / 2 : ℝ) ^ n ≤ ((3 / 4 : ℝ) ^ 2) ^ n :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have hsq : y / (2 : ℝ) ^ n ≤ (2 * (3 / 4 : ℝ) ^ n) ^ 2 := by
    calc
      _ = y * (1 / 2 : ℝ) ^ n := by rw [div_pow, one_pow]; ring
      _ ≤ 4 * ((3 / 4 : ℝ) ^ 2) ^ n :=
        mul_le_mul (by linarith : y ≤ 4) hn (by positivity) (by norm_num)
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul]; norm_num; ring
  exact (Real.sqrt_le_iff).mpr ⟨by positivity, hsq⟩

lemma size_dyadic_neg_nat {y : ℝ} (hy : 1 ≤ y) (n : ℕ) :
    sizeWeight (y / (2 : ℝ) ^ (-(n : ℤ))) ≤ 2 * (3 / 4 : ℝ) ^ n := by
  have hy0 : 0 < y := by linarith
  apply (size_le_inv _).trans
  have he : (y / (2 : ℝ) ^ (-(n : ℤ)))⁻¹ = y⁻¹ * (1 / 2 : ℝ) ^ n := by
    rw [_root_.zpow_neg, zpow_natCast, inv_div, div_eq_mul_inv, ← inv_pow]
    norm_num
    ring
  rw [he]
  have h₁ : y⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hy
  have h₂ : (1 / 2 : ℝ) ^ n ≤ (3 / 4 : ℝ) ^ n := pow_le_pow_left₀ (by norm_num) (by norm_num) n
  have h := mul_le_mul h₁ h₂ (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
  nlinarith [pow_nonneg (by norm_num : (0 : ℝ) ≤ 3 / 4) n]

lemma size_normalized {y : ℝ} (hy : 1 ≤ y) (hy2 : y ≤ 2) (n : ℤ) :
    sizeWeight (y / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ n.natAbs := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · simpa only [zpow_natCast, Int.natAbs_natCast] using size_dyadic_nat (by linarith) hy2 m
  · simpa only [Int.natAbs_neg, Int.natAbs_natCast] using size_dyadic_neg_nat hy m

lemma dyadic_normalize {x : ℝ} (hx : 0 < x) :
    ∃ k : ℤ, 1 ≤ x / (2 : ℝ) ^ k ∧ x / (2 : ℝ) ^ k ≤ 2 := by
  obtain ⟨k, hk, hk'⟩ := exists_mem_Ico_zpow hx (by norm_num : (1 : ℝ) < 2)
  refine ⟨k, (le_div_iff₀ (zpow_pos (by norm_num) k)).mpr (by simpa using hk), ?_⟩
  apply (div_le_iff₀ (zpow_pos (by norm_num) k)).mpr
  calc
    x ≤ (2 : ℝ) ^ (k + 1) := hk'.le
    _ = 2 * (2 : ℝ) ^ k := by rw [zpow_add_one₀ (by norm_num)]; ring

lemma size_shifted {x : ℝ} {k : ℤ} (hk : 1 ≤ x / (2 : ℝ) ^ k)
    (hk2 : x / (2 : ℝ) ^ k ≤ 2) (n : ℤ) :
    sizeWeight (x / (2 : ℝ) ^ n) ≤ 2 * (3 / 4 : ℝ) ^ (n - k).natAbs := by
  have he : x / (2 : ℝ) ^ n = (x / (2 : ℝ) ^ k) / (2 : ℝ) ^ (n - k) := by
    rw [zpow_sub₀ (by norm_num)]
    field_simp
  rw [he]
  exact size_normalized hk hk2 (n - k)

lemma hasSum_decay_nat : HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ n) 4 := by
  have h := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)
  norm_num at h
  exact h

lemma hasSum_decay_neg :
    HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ (-(n + 1 : ℤ)).natAbs) 3 := by
  have h := hasSum_decay_nat.mul_right (3 / 4 : ℝ)
  have he (n : ℕ) : (-(n + 1 : ℤ)).natAbs = n + 1 := by
    rw [Int.natAbs_neg, ← Nat.cast_one, ← Nat.cast_add, Int.natAbs_natCast]
  simp only [he, pow_succ]
  norm_num at h
  exact h

lemma hasSum_decay : HasSum (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) 7 := by
  have h₁ : HasSum (fun n : ℕ => (3 / 4 : ℝ) ^ (n : ℤ).natAbs) 4 := by
    simpa only [Int.natAbs_natCast] using hasSum_decay_nat
  have h : HasSum (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) (4 + 3) :=
    HasSum.of_nat_of_neg_add_one (f := fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs) h₁ hasSum_decay_neg
  norm_num at h
  exact h

lemma sum_decay_shift (S : Finset ℤ) (k : ℤ) :
    (∑ n ∈ S, (3 / 4 : ℝ) ^ (n - k).natAbs) ≤ 7 := by
  have hs : Summable (fun n : ℤ => (3 / 4 : ℝ) ^ (n - k).natAbs) :=
    hasSum_decay.summable.comp_injective (Equiv.subRight k).injective
  calc
    _ ≤ ∑' n : ℤ, (3 / 4 : ℝ) ^ (n - k).natAbs :=
      hs.sum_le_tsum S (fun _ _ => by positivity)
    _ = ∑' n : ℤ, (3 / 4 : ℝ) ^ n.natAbs :=
      by simpa only [Equiv.subRight_apply] using
        (Equiv.subRight k).tsum_eq (fun n : ℤ => (3 / 4 : ℝ) ^ n.natAbs)
    _ = 7 := hasSum_decay.tsum_eq

lemma sum_size_dyadic (S : Finset ℤ) {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ S, sizeWeight (x / (2 : ℝ) ^ n)) ≤ 14 := by
  obtain ⟨k, hk, hk2⟩ := dyadic_normalize hx
  calc
    _ ≤ ∑ n ∈ S, 2 * (3 / 4 : ℝ) ^ (n - k).natAbs :=
      Finset.sum_le_sum fun n _ => size_shifted hk hk2 n
    _ = 2 * ∑ n ∈ S, (3 / 4 : ℝ) ^ (n - k).natAbs := (Finset.mul_sum ..).symm
    _ ≤ 2 * 7 := mul_le_mul_of_nonneg_left (sum_decay_shift S k) (by norm_num)
    _ = 14 := by norm_num

lemma potential_rate_le_size {x : ℝ} (hx : 0 ≤ x) :
    PotentialScalar.rate x ≤ sizeWeight x := by
  by_cases h1 : x ≤ 1
  · rw [PotentialScalar.rate_small h1, PotentialScalar.sizeWeight_small hx h1]
  · have h1' : 1 ≤ x := le_of_lt (lt_of_not_ge h1)
    rw [PotentialScalar.rate_large h1', PotentialScalar.sizeWeight_large h1']
    have hi : 0 ≤ x⁻¹ := inv_nonneg.mpr hx
    have hi1 : x⁻¹ ≤ 1 := inv_le_one_of_one_le₀ h1'
    nlinarith

lemma gain_rate_le_size {x : ℝ} (hx : 0 ≤ x) :
    GainScalar.rate x ≤ sizeWeight x := by
  have hd : 0 < (1 + x) * Real.sqrt (1 + x) := by positivity
  apply le_min
  · rw [show exponent - 1 = (1 / 2 : ℝ) by norm_num [exponent], ← Real.sqrt_eq_rpow]
    unfold GainScalar.rate
    apply (div_le_iff₀ hd).mpr
    have hs : 1 ≤ Real.sqrt (1 + x) := Real.one_le_sqrt.mpr (by linarith)
    have hm : 1 ≤ (1 + x) * Real.sqrt (1 + x) := by
      have h := mul_le_mul (by linarith : (1 : ℝ) ≤ 1 + x) hs
        (by norm_num : (0 : ℝ) ≤ 1) (by positivity : 0 ≤ 1 + x)
      simpa only [one_mul] using h
    nlinarith [Real.sqrt_nonneg x]
  · by_cases hx0 : x = 0
    · simp [hx0, GainScalar.rate]
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      unfold GainScalar.rate
      apply (div_le_iff₀ hd).mpr
      apply (le_inv_mul_iff₀ hxpos).mpr
      calc
        x * Real.sqrt x ≤ (1 + x) * Real.sqrt (1 + x) :=
          mul_le_mul (by linarith) (Real.sqrt_le_sqrt (by linarith))
            (Real.sqrt_nonneg _) (by positivity)

lemma sum_rates_dyadic (S : Finset ℤ) {x : ℝ} (hx : 0 ≤ x) :
    (∑ n ∈ S, (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))) ≤ 28 := by
  by_cases hx0 : x = 0
  · simp [hx0, PotentialScalar.rate_zero_of_nonpos (le_refl (0 : ℝ)),
      GainScalar.extendedRate, GainScalar.rate]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  calc
    _ ≤ ∑ n ∈ S, 2 * sizeWeight (x / (2 : ℝ) ^ n) := by
      apply Finset.sum_le_sum
      intro n _
      have hn : 0 ≤ x / (2 : ℝ) ^ n := by positivity
      rw [GainScalar.extendedRate_eq hn]
      linarith [potential_rate_le_size hn, gain_rate_le_size hn]
    _ = 2 * ∑ n ∈ S, sizeWeight (x / (2 : ℝ) ^ n) := (Finset.mul_sum ..).symm
    _ ≤ 2 * 14 := mul_le_mul_of_nonneg_left (sum_size_dyadic S hxpos) (by norm_num)
    _ = 28 := by norm_num

end EuclideanSteinitz.Scale

namespace EuclideanSteinitz.ScaleMatrix
open Matrix MatrixEnergy Gain Energy Spectral
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma primitiveTrace_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    primitiveTrace A = hTrace A := by
  unfold primitiveTrace hTrace pTrace gainValue
  rw [Spectral.cfc_primitive_eq hA]
  congr 1
  congr 1
  apply cfc_congr
  intro x hx
  exact GainScalar.primitive_eq (spectrum_nonneg_of_nonneg hA.nonneg hx)

lemma primitiveTrace_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (t : ℝ) :
    HasDerivAt (fun u : ℝ => primitiveTrace (A + u • H))
      (rateMatrix (A + t • H) * H).trace t := by
  have hp := trace_semiconvex_affine_derivative hA hH PotentialScalar.primitive
    PotentialScalar.rate PotentialScalar.continuous_rate PotentialScalar.primitive_derivative
    PotentialScalar.convexified_convex t
  have hg := trace_semiconvex_affine_derivative hA hH GainScalar.primitive
    GainScalar.extendedRate GainScalar.continuous_extendedRate GainScalar.primitive_derivative
    GainScalar.convexified_convex t
  simpa only [primitiveTrace, rateMatrix, Matrix.add_mul, trace_add] using hp.fun_add hg

lemma rateMatrix_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (n : ℤ) :
    rateMatrix (((2 : ℝ) ^ n)⁻¹ • A) =
      cfc (fun x : ℝ => PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n)) A := by
  let f : ℝ → ℝ := fun x => PotentialScalar.rate x + GainScalar.extendedRate x
  have hf : Continuous f := PotentialScalar.continuous_rate.add GainScalar.continuous_extendedRate
  have he : cfc (fun x : ℝ => x / (2 : ℝ) ^ n) A = ((2 : ℝ) ^ n)⁻¹ • A := by
    simp only [div_eq_mul_inv, mul_comm _ (((2 : ℝ) ^ n)⁻¹)]
    rw [cfc_const_mul (((2 : ℝ) ^ n)⁻¹) (fun x : ℝ => x) A continuousOn_id,
      cfc_id' ℝ A hA.isSelfAdjoint]
  have hc := cfc_comp f (fun x : ℝ => x / (2 : ℝ) ^ n) A hA.isSelfAdjoint
    hf.continuousOn (by fun_prop)
  rw [he] at hc
  unfold rateMatrix
  rw [← cfc_add _ PotentialScalar.rate GainScalar.extendedRate
    PotentialScalar.continuous_rate.continuousOn GainScalar.continuous_extendedRate.continuousOn]
  exact hc.symm

lemma scaleRate_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ) :
    scaleRate S A = cfc (fun x : ℝ => ∑ n ∈ S,
      (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n))) A := by
  unfold scaleRate
  simp_rw [rateMatrix_cfc hA]
  symm
  have he : (fun x : ℝ => ∑ n ∈ S, (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))) = ∑ n ∈ S,
      (fun x : ℝ => PotentialScalar.rate (x / (2 : ℝ) ^ n) +
        GainScalar.extendedRate (x / (2 : ℝ) ^ n)) := by
    funext x
    simp only [Finset.sum_apply]
  rw [he]
  exact cfc_sum _ A S (fun _ _ => finite_spectrum_continuous _ _)

lemma scaleRate_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (S : Finset ℤ) :
    scaleRate S A ≤ (28 : ℝ) • (1 : Matrix ι ι ℝ) := by
  rw [scaleRate_cfc hA.1]
  let f : ℝ → ℝ := fun x => ∑ n ∈ S,
    (PotentialScalar.rate (x / (2 : ℝ) ^ n) +
      GainScalar.extendedRate (x / (2 : ℝ) ^ n))
  have hb : 0 ≤ cfc (fun x : ℝ => 28 - f x) A := by
    apply cfc_nonneg
    intro x hx
    exact sub_nonneg.mpr (Scale.sum_rates_dyadic S (spectrum_nonneg_of_nonneg hA.nonneg hx))
  rw [cfc_sub (fun _ : ℝ => 28) f A continuousOn_const (finite_spectrum_continuous _ _),
    cfc_const (28 : ℝ) A hA.1.isSelfAdjoint, Algebra.algebraMap_eq_smul_one] at hb
  exact sub_nonneg.mp hb

lemma scaleTrace_derivative {A H : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hH : H.IsHermitian) (S : Finset ℤ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => scaleTrace S (A + u • H))
      (scaleRate S (A + t • H) * H).trace t := by
  have hi (n : ℤ) : HasDerivAt
      (fun u : ℝ => (2 : ℝ) ^ n * primitiveTrace (((2 : ℝ) ^ n)⁻¹ • (A + u • H)))
      (rateMatrix (((2 : ℝ) ^ n)⁻¹ • (A + t • H)) * H).trace t := by
    have hd := (primitiveTrace_derivative (hA.smul (IsSelfAdjoint.all (((2 : ℝ) ^ n)⁻¹)))
      (hH.smul (IsSelfAdjoint.all (((2 : ℝ) ^ n)⁻¹))) t).const_mul ((2 : ℝ) ^ n)
    have he (u : ℝ) : ((2 : ℝ) ^ n)⁻¹ • (A + u • H) =
        ((2 : ℝ) ^ n)⁻¹ • A + u • (((2 : ℝ) ^ n)⁻¹ • H) := by
      simp only [smul_add, smul_smul, mul_comm]
    simp_rw [he]
    convert! hd using 1
    rw [Matrix.mul_smul, trace_smul, smul_eq_mul, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt (zpow_pos (by norm_num) n)), one_mul]
  have hs := HasDerivAt.sum (u := S) (fun n _ => hi n)
  convert! hs using 1
  · ext u
    simp only [scaleTrace, Finset.sum_apply]
  · simp only [scaleRate, Matrix.sum_mul, trace_sum]

lemma scaleTrace_mono_bound {A B : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hAB : A ≤ B) (S : Finset ℤ) :
    scaleTrace S B - scaleTrace S A ≤ 28 * (B.trace - A.trace) := by
  have hH : (B - A).PosSemidef := Matrix.le_iff.mp hAB
  have hd (t : ℝ) := scaleTrace_derivative hA.1 hH.1 S t
  have hb (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
      deriv (fun u : ℝ => scaleTrace S (A + u • (B - A))) t ≤ 28 * (B - A).trace := by
    rw [(hd t).deriv]
    have h := trace_mul_mono_right (scaleRate_le (hA.add (hH.smul ht.1)) S) hH
    simpa only [Matrix.smul_mul, Matrix.one_mul, trace_smul, smul_eq_mul] using h
  have hi := (convex_Icc (0 : ℝ) 1).image_sub_le_mul_sub_of_deriv_le
    (fun t _ => (hd t).continuousAt.continuousWithinAt)
    (fun t _ => (hd t).differentiableAt.differentiableWithinAt)
    (fun t ht => hb t (interior_subset ht)) 0 (by simp) 1 (by simp) (by norm_num)
  simpa only [zero_smul, one_smul, add_zero, add_sub_cancel, sub_zero, mul_one, trace_sub] using hi

lemma cfc_scaled {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) (c : ℝ) :
    cfc f (c • A) = cfc (fun x : ℝ => f (c * x)) A := by
  have he : cfc (fun x : ℝ => c * x) A = c • A := by
    rw [cfc_const_mul c (fun x : ℝ => x) A continuousOn_id, cfc_id' ℝ A hA.isSelfAdjoint]
  have hc := cfc_comp f (fun x : ℝ => c * x) A hA.isSelfAdjoint
    ((A.finite_real_spectrum.image _).continuousOn f) (by fun_prop)
  rw [he] at hc
  exact hc.symm

lemma scaleTrace_charpoly {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A.charpoly = B.charpoly) (S : Finset ℤ) :
    scaleTrace S A = scaleTrace S B := by
  unfold scaleTrace
  apply Finset.sum_congr rfl
  intro n _
  congr 1
  unfold primitiveTrace
  rw [cfc_scaled hA, cfc_scaled hA, cfc_scaled hB, cfc_scaled hB]
  rw [trace_cfc_eq_of_charpoly hA hB hAB, trace_cfc_eq_of_charpoly hA hB hAB]

lemma trace_charpoly {A B : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hAB : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rw [trace_spectral hA, trace_spectral hB,
    (hA.eigenvalues_eq_eigenvalues_iff hB).mpr hAB]

lemma scaleTrace_contraction_bound {A C : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hC : C * C.transpose ≤ 1) (T : Finset ℤ) :
    scaleTrace T A - scaleTrace T (C * A * C.transpose) ≤
      28 * (A.trace - (C * A * C.transpose).trace) := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian := (CFC.sqrt_nonneg A).posSemidef.1
  have hSS : S * S = A := by simpa only [← sq] using CFC.sq_sqrt A hA.nonneg
  have hCA : (C * A * C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using hA.mul_mul_conjTranspose_same C
  have hSC : (S * (C.transpose * C) * S).PosSemidef := by
    have hp : (C.transpose * C).PosSemidef := by
      simpa only [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial] using
        (star_mul_self_nonneg C : (0 : Matrix ι ι ℝ) ≤ star C * C).posSemidef
    simpa only [hS.eq] using hp.conjTranspose_mul_mul_same S
  have hle : S * (C.transpose * C) * S ≤ A := by
    have hp := (Matrix.le_iff.mp (transpose_contraction hC)).conjTranspose_mul_mul_same S
    rw [hS.eq] at hp
    apply Matrix.le_iff.mpr
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hSS] using hp
  have heq : (C * A * C.transpose).charpoly = (S * (C.transpose * C) * S).charpoly := by
    rw [← hSS]
    convert! charpoly_mul_comm (C * S) (S * C.transpose) using 1 <;> simp only [Matrix.mul_assoc]
  rw [scaleTrace_charpoly hCA.1 hSC.1 heq, trace_charpoly hCA.1 hSC.1 heq]
  exact scaleTrace_mono_bound hSC hle T

lemma scaleTrace_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef) (S : Finset ℤ) :
    scaleTrace S A = ∑ n ∈ S, (2 : ℝ) ^ n * hTrace (((2 : ℝ) ^ n)⁻¹ • A) := by
  apply Finset.sum_congr rfl
  intro n _
  rw [primitiveTrace_eq (hA.smul (by positivity))]

end EuclideanSteinitz.ScaleMatrix

namespace EuclideanSteinitz.ScaleEnergy
open Matrix MatrixEnergy Gain Energy ScaleMatrix
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
lemma rescale_old (c : ℝ) (p : Move ι) (A : Matrix ι ι ℝ) :
    (rescale c p).old (c • A) = c • p.old A := by
  simp only [rescale, Move.old, Matrix.mul_smul, Matrix.smul_mul]

omit [DecidableEq ι] in
lemma rescale_next (c : ℝ) (p : Move ι) (A : Matrix ι ι ℝ) :
    (rescale c p).next (c • A) = c • p.next A := by
  change (rescale c p).old (c • A) + c • p.gain = c • (p.old A + p.gain)
  rw [rescale_old, smul_add]

lemma aggregateCost_le_variation {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    aggregateCost S A ps ≤ 28 * variation A ps := by
  induction ps generalizing A with
  | nil => simp [aggregateCost, variation]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    have h₁ := scaleTrace_contraction_bound hA hp₀.1 S
    have h₂ := scaleTrace_mono_bound (p.old_psd hA) (Energy.Move.old_le_next hp₀ A) S
    have ht := ih (p.next_psd hp₀ hA) (fun q hq => hp q (List.mem_cons_of_mem p hq))
    change _ ≤ 28 * (_ + variation (p.next A) ps)
    dsimp only [aggregateCost]
    change scaleTrace S A - scaleTrace S (p.old A) ≤ 28 * (A.trace - (p.old A).trace) at h₁
    linarith

omit [DecidableEq ι] in
lemma variation_eq (A : Matrix ι ι ℝ) (ps : List (Move ι)) :
    variation A ps = A.trace + 2 * gainSum ps - (finish A ps).trace := by
  induction ps generalizing A with
  | nil => simp [variation, gainSum, finish]
  | cons p ps ih =>
    simp only [variation, gainSum, List.map_cons, List.sum_cons, finish, ih]
    rw [show (p.next A).trace = (p.old A).trace + p.gain.trace by
      simp only [Move.next, trace_add]]
    ring

lemma finish_psd {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) : (finish A ps).PosSemidef := by
  induction ps generalizing A with
  | nil => exact hA
  | cons p ps ih =>
    exact ih (p.next_psd (hp p (List.mem_cons_self ..)) hA)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))

lemma variation_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) :
    variation A ps ≤ A.trace + 2 * gainSum ps := by
  rw [variation_eq]
  exact sub_le_self _ (finish_psd hA hp).trace_nonneg

lemma sum_stepCost_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {p : Move ι} (hp : p.Admissible) (S : Finset ℤ) :
    (∑ n ∈ S, (2 : ℝ) ^ n * stepCost (rescale (((2 : ℝ) ^ n)⁻¹) p)
      (((2 : ℝ) ^ n)⁻¹ • A)) =
      scaleTrace S A - scaleTrace S (p.old A) + scaleTrace S (p.next A) - scaleTrace S (p.old A) := by
  rw [scaleTrace_eq hA, scaleTrace_eq (p.old_psd hA), scaleTrace_eq (p.next_psd hp hA)]
  simp only [stepCost, rescale_old, rescale_next, mul_sub, mul_add,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]

lemma aggregateCost_eq {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    aggregateCost S A ps = ∑ n ∈ S, (2 : ℝ) ^ n *
      cost (((2 : ℝ) ^ n)⁻¹ • A) (ps.map (rescale (((2 : ℝ) ^ n)⁻¹))) := by
  induction ps generalizing A with
  | nil => simp [aggregateCost, cost]
  | cons p ps ih =>
    have hp₀ := hp p (List.mem_cons_self ..)
    simp only [List.map_cons, cost, rescale_next, mul_add, Finset.sum_add_distrib]
    rw [sum_stepCost_eq hA hp₀, ← ih (p.next_psd hp₀ hA)
      (fun q hq => hp q (List.mem_cons_of_mem p hq))]
    rfl

lemma scale_energy_bound {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {ps : List (Move ι)} (hp : ∀ p ∈ ps, p.Admissible) (S : Finset ℤ) :
    (∑ n ∈ S, (2 : ℝ) ^ n *
      cost (((2 : ℝ) ^ n)⁻¹ • A) (ps.map (rescale (((2 : ℝ) ^ n)⁻¹)))) ≤
      28 * (A.trace + 2 * gainSum ps) := by
  rw [← aggregateCost_eq hA hp]
  exact (aggregateCost_le_variation hA hp S).trans
    (mul_le_mul_of_nonneg_left (variation_le hA hp) (by norm_num))

end EuclideanSteinitz.ScaleEnergy

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianTail
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Scalar and matrix Gaussian tail estimates. -/

section

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal

namespace GaussianTail

lemma integral_exp_square (t : ℝ) :
    (∫ x : ℝ, Real.exp (-t * x ^ 2 / 2) ∂gaussianReal 0 1) =
      (Real.sqrt (1 + t))⁻¹ := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
  have he (x : ℝ) : gaussianPDFReal 0 1 x * Real.exp (-t * x ^ 2 / 2) =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-((1 + t) / 2) * x ^ 2) := by
    simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  simp only [smul_eq_mul, he, integral_const_mul, integral_gaussian]
  rw [show Real.pi / ((1 + t) / 2) = (2 * Real.pi) / (1 + t) by rw [div_div_eq_mul_div]; ring]
  rw [Real.sqrt_div (by positivity : 0 ≤ 2 * Real.pi)]
  have hp : Real.sqrt (2 * Real.pi) ≠ 0 := by positivity
  field_simp

lemma inverse_sqrt_one_sub_le_exp {u : ℝ} (hu : 0 ≤ u) (hu' : u ≤ 1/2) :
    (Real.sqrt (1-u))⁻¹ ≤ Real.exp u := by
  have hpos : 0 < 1-u := by linarith
  have hlog : -Real.log (1-u) ≤ 2*u := by
    have h := Real.log_le_sub_one_of_pos (inv_pos.mpr hpos)
    rw [Real.log_inv] at h
    have hi : (1-u)⁻¹ - 1 ≤ 2*u := by
      rw [inv_eq_one_div]
      apply (sub_le_iff_le_add).mpr
      apply (div_le_iff₀ hpos).mpr
      nlinarith
    exact h.trans hi
  apply (Real.log_le_log_iff (inv_pos.mpr (Real.sqrt_pos.mpr hpos)) (Real.exp_pos u)).mp
  rw [Real.log_inv, Real.log_sqrt hpos.le, Real.log_exp]
  linarith

open Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma quadratic_eigenbasis {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (x : ι → ℝ) :
    ⟪∑ i, x i • hA.eigenvectorBasis i,
      toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ =
      ∑ i, hA.eigenvalues i * x i ^ 2 := by
  have he (i : ι) : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simp only [map_sum, map_smul, he, smul_smul,
    sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    hA.eigenvectorBasis.inner_eq_ite]
  simp [mul_ite, ite_mul, pow_two, mul_comm, mul_left_comm, mul_assoc]

lemma quadratic_mgf_eq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) = ∏ i, (Real.sqrt (1-hA.eigenvalues i))⁻¹ := by
  have he (x : ι → ℝ) :
      Real.exp (⟪∑ i, x i • hA.eigenvectorBasis i,
        toEuclideanCLM (𝕜 := ℝ) A (∑ i, x i • hA.eigenvectorBasis i)⟫ / 2) =
      ∏ i, Real.exp (hA.eigenvalues i * x i ^ 2 / 2) := by
    rw [quadratic_eigenbasis, ← Real.exp_sum]
    congr 1
    simp only [Finset.sum_div]
  rw [stdGaussian_eq_map_pi_orthonormalBasis hA.eigenvectorBasis,
    integral_map (Measurable.aemeasurable (by fun_prop)) (by fun_prop)]
  simp only [he]
  rw [integral_fintype_prod_eq_prod
    (f := fun i (x : ℝ) => Real.exp (hA.eigenvalues i * x ^ 2 / 2))]
  apply Finset.prod_congr rfl
  intro i _
  simpa only [neg_neg, sub_eq_add_neg] using integral_exp_square (-hA.eigenvalues i)

lemma quadratic_mgf_le {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hEig : ∀ i, hA.1.eigenvalues i ≤ 1/2) :
    (∫ x : EuclideanSpace ℝ ι, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2)
      ∂stdGaussian (EuclideanSpace ℝ ι)) ≤ Real.exp A.trace := by
  rw [quadratic_mgf_eq hA.1, hA.1.trace_eq_sum_eigenvalues,
    Real.exp_sum]
  apply Finset.prod_le_prod₀
  · intro i _
    positivity
  · intro i _
    exact inverse_sqrt_one_sub_le_exp (hA.eigenvalues_nonneg i) (hEig i)

lemma quadratic_mgf_integrable {A : Matrix ι ι ℝ} (hA : A.IsHermitian)
    (hEig : ∀ i, hA.eigenvalues i < 1) :
    Integrable (fun x : EuclideanSpace ℝ ι => Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ / 2))
      (stdGaussian (EuclideanSpace ℝ ι)) := by
  apply Integrable.of_integral_ne_zero
  rw [quadratic_mgf_eq hA]
  apply ne_of_gt
  exact Finset.prod_pos fun i _ => inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [hEig i]))

lemma quadratic_tail {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    (hEig : ∀ i, hA.1.eigenvalues i ≤ 1/2) (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι)
      {x | 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  let f := fun x : EuclideanSpace ℝ ι =>
    Real.exp (-A.trace-r) * Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫/2)
  have hi : Integrable f (stdGaussian (EuclideanSpace ℝ ι)) :=
    (quadratic_mgf_integrable hA.1 (fun i => by linarith [hEig i])).const_mul _
  have hbound := hi.measure_le_integral (Filter.Eventually.of_forall fun x =>
    mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
    (s := {x | 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫})
    (fun x hx => by
      dsimp only [f]
      rw [← Real.exp_add]
      exact Real.one_le_exp_iff.mpr (by
        change 2*(A.trace+r) ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ at hx
        linarith))
  apply hbound.trans
  apply ENNReal.ofReal_le_ofReal
  rw [show (∫ x, f x ∂stdGaussian (EuclideanSpace ℝ ι)) =
      Real.exp (-A.trace-r) * ∫ x, Real.exp (⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫/2)
        ∂stdGaussian (EuclideanSpace ℝ ι) by exact integral_const_mul _ _]
  calc
    _ ≤ Real.exp (-A.trace-r) * Real.exp A.trace :=
      mul_le_mul_of_nonneg_left (quadratic_mgf_le hA hEig) (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

lemma eigenvalue_le_of_form_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {b : ℝ}
    (hb : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ b*‖x‖^2) :
    ∀ i, hA.eigenvalues i ≤ b := by
  intro i
  have h := hb (hA.eigenvectorBasis i)
  rw [hA.eigenvectorBasis.orthonormal.norm_eq_one, one_pow, mul_one] at h
  have he : toEuclideanCLM (𝕜 := ℝ) A (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    apply WithLp.ofLp_injective
    exact hA.mulVec_eigenvectorBasis i
  simpa [he, real_inner_smul_right, hA.eigenvectorBasis.inner_eq_ite] using h

lemma scaled_quadratic_tail {A : Matrix ι ι ℝ} (hA : A.PosSemidef)
    {b : ℝ} (hb : 0 < b)
    (hform : ∀ x : EuclideanSpace ℝ ι, ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ b*‖x‖^2)
    (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι)
      {x | 2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} ≤
        ENNReal.ofReal (Real.exp (-r)) := by
  let S : Matrix ι ι ℝ := (1/(2*b)) • A
  have hS : S.PosSemidef := hA.smul (by positivity : 0 ≤ 1/(2*b))
  have he (x : EuclideanSpace ℝ ι) : ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫ =
      (1/(2*b))*⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫ := by
    simp only [S, inner_toEuclideanCLM, smul_mulVec, dotProduct_smul, smul_eq_mul]
  have hspec : ∀ i, hS.1.eigenvalues i ≤ 1/2 := by
    apply eigenvalue_le_of_form_le hS.1
    intro x
    rw [he]
    have hx := mul_le_mul_of_nonneg_left (hform x) (by positivity : 0 ≤ 1/(2*b))
    apply hx.trans_eq
    field_simp
  have hset : {x : EuclideanSpace ℝ ι | 2*S.trace+2*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫} =
      {x | 2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫} := by
    ext x
    change (2*S.trace+2*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) S x⟫) ↔
      2*A.trace+4*b*r ≤ ⟪x, toEuclideanCLM (𝕜 := ℝ) A x⟫
    simp only [he, S, trace_smul, smul_eq_mul]
    constructor <;> intro h
    · have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 2*b)
      field_simp at hm
      nlinarith
    · have hm := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 1/(2*b))
      field_simp at hm ⊢
      nlinarith
  have ht := quadratic_tail hS hspec r
  rw [show 2*(S.trace+r)=2*S.trace+2*r by ring, hset] at ht
  exact ht

end GaussianTail

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace ENNReal
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma squareMass_nonneg (B : Matrix κ ι ℝ) : 0 ≤ squareMass B := by
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma gram_form (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ⟪x,toEuclideanCLM (𝕜 := ℝ) (B.transpose*B) x⟫ = ‖matrixMap B x‖^2 := by
  rw [inner_toEuclideanCLM,← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
  rw [← real_inner_self_eq_norm_sq]
  rfl

omit [DecidableEq ι] in
lemma gram_trace (B : Matrix κ ι ℝ) : (B.transpose*B).trace = squareMass B := by
  change (∑ i,∑ j,B j i*B j i) = ∑ i,∑ j,B i j^2
  simp only [← sq]
  exact Finset.sum_comm

lemma norm_sq_le_squareMass (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) :
    ‖matrixMap B x‖^2 ≤ squareMass B*‖x‖^2 := by
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  change (∑ i,(∑ j,B i j*x j)^2) ≤ (∑ i,∑ j,B i j^2)*(∑ j,x j^2)
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun i _ => Finset.sum_mul_sq_le_sq_mul_sq _ _ _

lemma matrix_square_tail (B : Matrix κ ι ℝ) {b : ℝ} (hb : 0 < b)
    (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ b*‖x‖^2) (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι) {x | 2*squareMass B+4*b*r ≤ ‖matrixMap B x‖^2} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  have hA : (B.transpose*B).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_conjTranspose_mul_self B
  simpa only [gram_trace,gram_form] using scaled_quadratic_tail hA hb
    (fun x => by rw [gram_form]; exact hB x) r

lemma interpolated_form (B : Matrix κ ι ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hS : squareMass B ≤ v) (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ 4*‖x‖^2) :
    ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ (2*Real.sqrt v)*‖x‖^2 := by
  intro x
  by_cases h : v ≤ 4
  · apply (norm_sq_le_squareMass B x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply hS.trans
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : Real.sqrt v ≤ 2 := (Real.sqrt_le_iff).mpr ⟨by norm_num,by nlinarith⟩
    nlinarith
  · apply (hB x).trans
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hs := Real.sq_sqrt hv
    have hp := Real.sqrt_nonneg v
    have hle : 2 ≤ Real.sqrt v := (Real.le_sqrt (by norm_num) hv).mpr (by linarith)
    linarith

lemma interpolated_tail (B : Matrix κ ι ℝ) {v : ℝ} (hv : 0 < v)
    (hS : squareMass B ≤ v) (hB : ∀ x : EuclideanSpace ℝ ι,‖matrixMap B x‖^2 ≤ 4*‖x‖^2)
    (r : ℝ) :
    stdGaussian (EuclideanSpace ℝ ι) {x | 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2} ≤
      ENNReal.ofReal (Real.exp (-r)) := by
  apply (measure_mono (show {x | 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2} ⊆
    {x | 2*squareMass B+4*(2*Real.sqrt v)*r ≤ ‖matrixMap B x‖^2} from ?_)).trans
  · exact matrix_square_tail B (by positivity) (interpolated_form B hv.le hS hB) r
  · intro x hx
    change 2*v+8*Real.sqrt v*r ≤ ‖matrixMap B x‖^2 at hx
    change 2*squareMass B+4*(2*Real.sqrt v)*r ≤ ‖matrixMap B x‖^2
    linarith

end GaussianTail

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilterMoments
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered moments, prefix bounds, and rank-one contractions. -/

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma cutoff_size {x : ℝ} (hx : 0 ≤ x) (hf : cutoff x≠0) : 1/4 ≤ sizeWeight x := by
  have hb : 1/2 ≤ x ∧ x ≤ 4 := by
    by_contra h
    exact hf (cutoff_zero_of_not_band h)
  have hp : 0<x := by linarith
  unfold sizeWeight
  rw [show exponent-1=(1/2:ℝ) by norm_num [exponent],← Real.sqrt_eq_rpow]
  apply le_min
  · exact (Real.le_sqrt (by norm_num) hx).mpr (by nlinarith)
  · exact (le_inv_comm₀ (by norm_num) hp).mpr (by norm_num; linarith)

lemma cutoff_square_size {x : ℝ} (hx : 0 ≤ x) : cutoff x^2 ≤ 4*sizeWeight x := by
  by_cases hf : cutoff x=0
  · rw [hf,zero_pow (by decide : 2≠0)]; positivity [Scale.size_nonneg hx]
  · have hs := cutoff_size hx hf
    have ha := cutoff_nonneg x
    have hb := cutoff_le_one x
    nlinarith

lemma cutoff_scaled_size {x : ℝ} (hx : 0 ≤ x) : x*cutoff x^2 ≤ 16*sizeWeight x := by
  by_cases hf : cutoff x=0
  · rw [hf,zero_pow (by decide : 2≠0),mul_zero]; positivity [Scale.size_nonneg hx]
  · have hb : x ≤ 4 := by
      by_contra h
      exact hf (cutoff_zero_of_not_band (by tauto))
    have hs := cutoff_size hx hf
    have ha := cutoff_nonneg x
    have hc := cutoff_le_one x
    have ht : cutoff x^2 ≤ 1 := by nlinarith
    nlinarith [mul_le_mul_of_nonneg_left ht hx]

omit [DecidableEq κ] in
lemma squareMass_weighted (B : Matrix κ ι ℝ) : squareMass B=weightedSq B 1 := by
  rw [weightedSq,Matrix.mul_one,Matrix.trace_mul_comm,gram_trace]

omit [DecidableEq κ] in
lemma squareMass_le_weighted (B : Matrix κ ι ℝ) {q : ι → ℝ} (hq : ∀ i,0 ≤ q i) :
    squareMass B ≤ weightedSq B (1+diagonal q) := by
  rw [weightedSq_weight_add,← squareMass_weighted]
  exact le_add_of_nonneg_right (weightedSq_nonneg B (PosSemidef.diagonal hq))

lemma coisometry_norm_le {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) : ‖R‖ ≤ 1 := by
  have he := Matrix.l2_opNorm_conjTranspose_mul_self R.transpose
  simp only [conjTranspose_eq_transpose_of_trivial,transpose_transpose,hR] at he
  have ht : ‖R.transpose‖=‖R‖ := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using Matrix.l2_opNorm_conjTranspose R
  have ho : ‖(1 : Matrix ι ι ℝ)‖ ≤ 1 := by
    rw [← Matrix.diagonal_one,Matrix.l2_opNorm_diagonal]
    exact (pi_norm_le_iff_of_nonneg (by norm_num)).mpr (fun _ => by norm_num)
  rw [ht] at he
  nlinarith [norm_nonneg R]

lemma cutoff_norm_le (X : Matrix ι ι ℝ) : ‖cfc cutoff X‖ ≤ 1 := by
  apply norm_cfc_le (by norm_num)
  intro x _
  rw [Real.norm_eq_abs,abs_of_nonneg (cutoff_nonneg x)]
  exact cutoff_le_one x

lemma lift_cutoff_contract {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {X : Matrix ι ι ℝ} (_hX : X.IsHermitian) (x : EuclideanSpace ℝ κ) :
    ‖matrixMap (lift R (cfc cutoff X)) x‖^2 ≤ ‖x‖^2 := by
  have hr := coisometry_norm_le hR
  have ht : ‖R.transpose‖ ≤ 1 := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      (Matrix.l2_opNorm_conjTranspose R).le.trans hr
  have hn : ‖lift R (cfc cutoff X)‖ ≤ 1 := by
    exact (Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul
      ((Matrix.l2_opNorm_mul _ _).trans ((mul_le_mul ht (cutoff_norm_le X)
        (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))) hr
      (norm_nonneg _) (by norm_num)).trans_eq (one_mul _))
  have hv : ‖matrixMap (lift R (cfc cutoff X)) x‖ ≤ ‖x‖ := by
    exact (Matrix.l2_opNorm_mulVec _ x).trans
      ((mul_le_mul_of_nonneg_right hn (norm_nonneg x)).trans_eq (one_mul _))
  exact pow_le_pow_left₀ (norm_nonneg _) hv 2

lemma lift_cutoff_mass {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {X : Matrix ι ι ℝ} (hX : X.PosSemidef) :
    squareMass (lift R (cfc cutoff X)) ≤ 4*(cfc sizeWeight X).trace := by
  rw [squareMass_weighted,weighted_lift R hR,Matrix.mul_one,hR,
    weightedSq_cfc hX.1,Matrix.mul_one,trace_cfc hX.1,trace_cfc hX.1,Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => cutoff_square_size (hX.eigenvalues_nonneg i)

omit [Fintype κ] [DecidableEq κ] in
lemma lift_cutoff_size {R : Matrix ι κ ℝ} {X : Matrix ι ι ℝ} (hX : X.PosSemidef)
    (hf : lift R (cfc cutoff X)≠0) : 1/4 ≤ (cfc sizeWeight X).trace := by
  have he : ∃ i,cutoff (hX.1.eigenvalues i)≠0 := by
    by_contra! h
    apply hf
    rw [real_cfc hX.1]
    simp [h,lift]
  obtain ⟨i,hi⟩ := he
  rw [trace_cfc hX.1]
  exact (cutoff_size (hX.eigenvalues_nonneg i) hi).trans
    (Finset.single_le_sum (fun j _ => Scale.size_nonneg (hX.eigenvalues_nonneg j)) (Finset.mem_univ i))

omit [DecidableEq κ] in
lemma weightedSq_diagonal_mono (B : Matrix κ ι ℝ) {q r : ι → ℝ}
    (hqr : ∀ i,q i ≤ r i) : weightedSq B (diagonal q) ≤ weightedSq B (diagonal r) := by
  have hp : (diagonal (fun i => r i-q i)).PosSemidef :=
    PosSemidef.diagonal (fun i => sub_nonneg.mpr (hqr i))
  have hh := weightedSq_nonneg B hp
  have he : diagonal r=diagonal q+diagonal (fun i => r i-q i) := by
    rw [diagonal_add]; congr 1; funext i; simp
  rw [he,weightedSq_weight_add]
  linarith

lemma lift_cutoff_time {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0<q j) {θ : ℝ} (hθ : 0<θ) :
    weightedSq (lift R (cfc cutoff (state (fun j => q j/θ) R))) (diagonal q) ≤
      16*(cfc sizeWeight (state (fun j => q j/θ) R)).trace*θ := by
  let X := state (fun j => q j/θ) R
  have hX : X.PosDef := state_posDef hR (fun j => div_pos (hq j) hθ)
  have he : R*diagonal q*R.transpose=θ • X := by
    dsimp [X,state]
    have hd : θ • diagonal (fun j => q j/θ)=diagonal q := by
      rw [← Matrix.diagonal_smul]
      congr 1
      funext j
      change θ*(q j/θ)=q j
      field_simp
    rw [← Matrix.smul_mul,← Matrix.mul_smul,hd]
  have hec : cfc (fun x => cutoff x^2) X*X=cfc (fun x => cutoff x^2*x) X := by
    conv_lhs => arg 2; rw [← cfc_id' ℝ X hX.1.isSelfAdjoint]
    exact cfc_mul_same hX.1 _ _
  rw [weighted_lift R hR,he,weightedSq_cfc hX.1,Matrix.mul_smul,Matrix.trace_smul,hec,
    trace_cfc hX.1,trace_cfc hX.1]
  change θ*(∑ i,cutoff (hX.1.eigenvalues i)^2*hX.1.eigenvalues i) ≤ _
  have hh := Finset.sum_le_sum (fun (i : ι) (_ : i∈Finset.univ) =>
    cutoff_scaled_size (hX.eigenvalues_pos i).le)
  rw [← Finset.mul_sum] at hh
  have hh' : (∑ i,cutoff (hX.1.eigenvalues i)^2*hX.1.eigenvalues i) ≤
      16*∑ i,sizeWeight (hX.1.eigenvalues i) := by simpa only [mul_comm] using hh
  nlinarith

end EuclideanSteinitz.Filter

end

section

namespace EuclideanSteinitz.Energy
open Matrix Gain
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma cost_append (A : Matrix ι ι ℝ) (ps qs : List (Move ι)) :
    cost A (ps++qs)=cost A ps+cost (finish A ps) qs := by
  induction ps generalizing A with
  | nil => simp [cost,finish]
  | cons p ps ih => simp only [List.cons_append,cost,finish,ih,add_assoc]

lemma cost_prefix {A : Matrix ι ι ℝ} (hA : A.PosSemidef) {ps qs : List (Move ι)}
    (hp : ∀ p∈qs,p.Admissible) (h : ps <+: qs) : cost A ps ≤ cost A qs := by
  obtain ⟨rs,rfl⟩ := h
  rw [cost_append]
  exact le_add_of_nonneg_right (cost_nonneg
    (EuclideanSteinitz.ScaleEnergy.finish_psd hA (fun p h => hp p (List.mem_append_left _ h)))
    (fun p h => hp p (List.mem_append_right _ h)))

end EuclideanSteinitz.Energy

namespace EuclideanSteinitz.Filter
open Matrix MatrixEnergy Gain Energy
open scoped MatrixOrder Matrix.Norms.L2Operator
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype κ] [DecidableEq ι] in
lemma run_append (R : Matrix ι κ ℝ) (ps qs : List (Step ι κ)) :
    run R (ps++qs)=run (run R ps) qs := by
  induction ps generalizing R with
  | nil => rfl
  | cons p ps ih => exact ih (p.apply R)

omit [Fintype κ] [DecidableEq ι] in
lemma run_fresh_append {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)}
    (hf : Fresh R (ps++qs)) (hd : ((ps++qs).map Step.j).Nodup) : Fresh (run R ps) qs := by
  induction ps generalizing R with
  | nil => exact hf
  | cons p ps ih =>
    have hh := List.nodup_cons.mp hd
    apply ih (R := p.apply R) _ hh.2
    apply Step.fresh_tail hf
    intro q hq he
    exact hh.1 (List.mem_map.mpr ⟨q,hq,he.symm⟩)

omit [Fintype κ] [DecidableEq κ] in
lemma good_prefix {ps qs : List (Step ι κ)} (hp : ∀ p∈qs,p.Good) (h : ps <+: qs) :
    ∀ p∈ps,p.Good := fun p hp' => hp p (h.subset hp')

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma fresh_prefix {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)} (hf : Fresh R qs) (h : ps <+: qs) :
    Fresh R ps := fun p hp => hf p (h.subset hp)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma nodup_prefix {ps qs : List (Step ι κ)} (hd : (qs.map Step.j).Nodup) (h : ps <+: qs) :
    (ps.map Step.j).Nodup := (h.map _).sublist.nodup hd

omit [Fintype κ] [DecidableEq κ] in
lemma moves_good {ps : List (Step ι κ)} (hp : ∀ p∈ps,p.Good) {q : κ → ℝ} (hq : ∀ j,0≤q j) :
    ∀ p∈ps.map (fun p => p.move q),p.Admissible := by
  intro p hp'
  obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hp'
  exact Step.admissible (hp r hr) hq

lemma cost_prefix_difference {R : Matrix ι κ ℝ} {ps qs : List (Step ι κ)}
    (hf : Fresh R (ps++qs)) (hd : ((ps++qs).map Step.j).Nodup) (q : κ → ℝ) :
    cost (state q R) ((ps++qs).map (fun p => p.move q)) -
      cost (state q R) (ps.map (fun p => p.move q)) =
      cost (state q (run R ps)) (qs.map (fun p => p.move q)) := by
  rw [List.map_append,cost_append,← run_state q (fresh_prefix hf (List.prefix_append _ _))
    (nodup_prefix hd (List.prefix_append _ _))]
  ring

lemma local_prefix_increment {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    {ps qs : List (Step ι κ)} (hps : ps <+: qs) (hqs : qs <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j)
    (hsmall : cost (state q R) (qs.map (fun p => p.move q)) -
      cost (state q R) (ps.map (fun p => p.move q)) ≤ 1/(16*gainConstant)) :
    Coefficient.weightedSq
      (Coefficient.lift (run R qs) (cfc cutoff (state q (run R qs))) -
       Coefficient.lift (run R ps) (cfc cutoff (state q (run R ps)))) (1+diagonal q) ≤
      incrementConstant*(1+(cfc sizeWeight (state q (run R qs))).trace)*
      (cost (state q R) (qs.map (fun p => p.move q)) -
       cost (state q R) (ps.map (fun p => p.move q)))^(1/exponent) := by
  obtain ⟨rs,rfl⟩ := hps
  have hp' := good_prefix hp hqs
  have hf' := fresh_prefix hf hqs
  have hd' := nodup_prefix hd hqs
  have hc := cost_prefix_difference hf' hd' q
  rw [hc] at hsmall ⊢
  rw [run_append]
  exact weighted_increment
    (run_coisometry hR (good_prefix hp' (List.prefix_append _ _))
      (fresh_prefix hf' (List.prefix_append _ _)) (nodup_prefix hd' (List.prefix_append _ _)))
    (fun p h => hp' p (List.mem_append_right _ h)) (run_fresh_append hf' hd')
    (by rw [List.map_append] at hd'; exact (List.nodup_append.mp hd').2.1)
    hq le_rfl hsmall

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleEnergy Energy
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

lemma coisometry_column {R : Matrix ι κ ℝ} (hR : R*R.transpose=1) (j : κ) :
    (∑ i,R i j^2) ≤ 1 := by
  have h := Matrix.l2_opNorm_mulVec R (EuclideanSpace.single j (1:ℝ))
  have hn : ‖(EuclideanSpace.single j (1:ℝ))‖=1 := by simp
  rw [hn,mul_one] at h
  have hh : ‖matrixMap R (EuclideanSpace.single j 1)‖≤1 := h.trans (coisometry_norm_le hR)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hh 2
  rw [EuclideanSpace.real_norm_sq_eq] at hs
  simpa [matrixMap,Matrix.toEuclideanLin,Matrix.mulVec,PiLp.single_apply] using hs

lemma state_trace_le {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) : (state q R).trace ≤ ∑ j,q j := by
  calc
    _ = ∑ j,q j*(∑ i,R i j^2) := by
      change (∑ i,∑ j,(R*diagonal q) i j*R.transpose j i)=_
      simp only [Matrix.mul_diagonal,Matrix.transpose_apply]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ j,q j := Finset.sum_le_sum fun j _ => by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left (coisometry_column hR j) (hq j)

omit [Fintype κ] [DecidableEq κ] in
lemma Step.b_square_le {p : Step ι κ} (hp : p.Good) : ∑ i,p.b i^2 ≤ 1 := by
  have hc : (p.C*p.C.transpose).PosSemidef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using posSemidef_self_mul_conjTranspose p.C
  have he : p.C*p.C.transpose = 1-vecMulVec p.b p.b := by rw [← hp.2]; abel
  rw [he] at hc
  have hh := hc.dotProduct_mulVec_nonneg p.b
  simp only [star_trivial,Matrix.sub_mulVec,Matrix.one_mulVec,dotProduct_sub,
    Matrix.vecMulVec_mulVec,dotProduct_smul,op_smul_eq_mul] at hh
  have hbb : p.b ⬝ᵥ p.b=∑ i,p.b i^2 := by simp only [dotProduct,pow_two]
  rw [hbb] at hh
  nlinarith [Finset.sum_nonneg (fun i (_ : i∈Finset.univ) => sq_nonneg (p.b i))]

lemma gains_le_total {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hd : (L.map Step.j).Nodup)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) : gainSum (L.map (fun p => p.move q)) ≤ ∑ j,q j := by
  have hterm (p : Step ι κ) (h : p∈L) : (p.move q).gain.trace ≤ q p.j := by
    change (q p.j • vecMulVec p.b p.b).trace ≤ _
    rw [Matrix.trace_smul]
    have ht : (vecMulVec p.b p.b).trace=∑ i,p.b i^2 := by simp [Matrix.trace,vecMulVec_apply,pow_two]
    rw [ht,smul_eq_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (Step.b_square_le (hp p h)) (hq p.j)
  calc
    gainSum (L.map (fun p => p.move q)) = (L.map (fun p => (p.move q).gain.trace)).sum := by simp only [gainSum,List.map_map,Function.comp_def]
    _ ≤ (L.map (fun p => q p.j)).sum := List.sum_le_sum hterm
    _ = ∑ j∈(L.map Step.j).toFinset,q j := by
      rw [List.sum_toFinset _ hd]
      simp only [List.map_map,Function.comp_def]
    _ ≤ ∑ j,q j := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ => hq j)

omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma move_scale (p : Step ι κ) (q : κ → ℝ) (θ : ℝ) :
    p.move (fun j => q j/θ) = rescale θ⁻¹ (p.move q) := by
  cases p
  simp only [Step.move,rescale]
  congr 1
  rw [smul_smul]
  congr 1
  simp [div_eq_mul_inv,mul_comm]

lemma sum_epoch_cost {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hd : (L.map Step.j).Nodup)
    {q : κ → ℝ} (hq : ∀ j,0≤q j) (S : Finset ℤ) :
    (∑ k∈S,(2:ℝ)^k*cost (((2:ℝ)^k)⁻¹ • state q R)
      (L.map (fun p => p.move (fun j => q j/(2:ℝ)^k)))) ≤ 84*(∑ j,q j) := by
  simp only [move_scale,show ∀ c, L.map (fun p => rescale c (p.move q)) =
    (L.map (fun p => p.move q)).map (rescale c) from fun c => by simp only [List.map_map,Function.comp_def]]
  have hstate : (state q R).PosSemidef := by
    change (R*diagonal q*R.transpose).PosSemidef
    simpa only [conjTranspose_eq_transpose_of_trivial] using (PosSemidef.diagonal hq).mul_mul_conjTranspose_same R
  exact (scale_energy_bound hstate (moves_good hp hq) S).trans (by
    have h₁ := state_trace_le hR hq
    have h₂ := gains_le_total hp hd hq
    linarith)

lemma sum_dyadic_le {S : Finset ℤ} {b : ℝ} (hb : 0≤b) (hS : ∀ k∈S,(2:ℝ)^k≤b) :
    (∑ k∈S,(2:ℝ)^k) ≤ 2*b := by
  classical
  by_cases hne : S.Nonempty
  · let M := S.max' hne
    have hM k (hk : k∈S) : k≤M := Finset.le_max' S k hk
    let f := fun k : ℤ => (M-k).toNat
    have hinj : Set.InjOn f S := by
      intro k hk l hl h
      have hk' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM k hk))
      have hl' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM l hl))
      have := congrArg (fun n : ℕ => (n:ℤ)) h
      dsimp [f] at this
      omega
    have he k (hk : k∈S) : (2:ℝ)^k = (2:ℝ)^M*(1/2:ℝ)^(f k) := by
      have hk' := Int.toNat_of_nonneg (sub_nonneg.mpr (hM k hk))
      rw [one_div,inv_pow,← zpow_natCast]
      dsimp [f]
      rw [hk',← _root_.zpow_neg,← zpow_add₀ (by norm_num)]
      congr 1
      ring
    have hsum : (∑ k∈S,(1/2:ℝ)^(f k)) ≤ 2 := by
      rw [← Finset.sum_image hinj]
      have hs := hasSum_geometric_of_lt_one (by norm_num : (0:ℝ)≤1/2) (by norm_num : (1/2:ℝ)<1)
      have hh := hs.summable.sum_le_tsum (S.image f) (fun n _ => by positivity)
      rw [hs.tsum_eq] at hh
      norm_num at hh
      exact hh
    calc
      _ = (2:ℝ)^M*∑ k∈S,(1/2:ℝ)^(f k) := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl he
      _ ≤ (2:ℝ)^M*2 := mul_le_mul_of_nonneg_left hsum (zpow_pos (by norm_num) _).le
      _ ≤ 2*b := by nlinarith [hS M (Finset.max'_mem S hne)]
  · simp only [Finset.not_nonempty_iff_eq_empty.mp hne,Finset.sum_empty]
    positivity

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.GaussianProcess
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Stationary Gaussian autoregressive rows and covariance identities. -/

section

open Matrix
open scoped BigOperators
namespace GaussianAR

lemma row_dot_step (r : ℝ) (n t u : ℕ) (ht : t<n) :
    (∑ k ∈ Finset.range (n+1), row r (t+1) k*row r u k) =
      r*(∑ k ∈ Finset.range (n+1), row r t k*row r u k)+
        Real.sqrt (1-r^2)*row r u (t+1) := by
  simp only [row,add_mul,ite_mul,zero_mul,Finset.sum_add_distrib,mul_assoc,← Finset.mul_sum]
  congr 1
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_range,show t+1<n+1 by omega,ite_true]

lemma row_norm (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n t : ℕ) (ht : t≤n) :
    (∑ k ∈ Finset.range (n+1), (row r t k)^2)=1 := by
  have hs : 0 ≤ 1-r^2 := by nlinarith
  induction t with
  | zero => simp [row]
  | succ t ih =>
    have hp := ih (by omega)
    have hcross : (∑ k ∈ Finset.range (n+1), row r t k*(if k=t+1 then Real.sqrt (1-r^2) else 0))=0 := by
      simp only [mul_ite,mul_zero,Finset.sum_ite_eq',Finset.mem_range,show t+1<n+1 by omega,ite_true]
      rw [row_support r (by omega),zero_mul]
    have he (k : ℕ) : (row r (t+1) k)^2 = r^2*(row r t k)^2+
        2*r*(row r t k*(if k=t+1 then Real.sqrt (1-r^2) else 0))+
        (if k=t+1 then (Real.sqrt (1-r^2))^2 else 0) := by
      rw [row]
      split_ifs <;> ring
    simp only [he,Finset.sum_add_distrib,← Finset.mul_sum,hp,hcross,mul_zero,add_zero]
    rw [Finset.sum_ite_eq']
    simp only [Finset.mem_range,show t+1<n+1 by omega,ite_true,mul_one,Real.sq_sqrt hs]
    ring

lemma row_covariance (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (n t u : ℕ) (ht : t≤n) (hu : u≤t) :
    (∑ k ∈ Finset.range (n+1), row r t k*row r u k)=r^(t-u) := by
  induction t with
  | zero =>
    have : u=0 := by omega
    subst u
    simp [row]
  | succ t ih =>
    by_cases h : u=t+1
    · subst u
      simpa only [Nat.sub_self,pow_zero,← sq] using row_norm r hr hr1 n (t+1) ht
    · have hu' : u≤t := by omega
      rw [row_dot_step r n t u (by omega),ih (by omega) hu',row_support r (by omega),mul_zero,add_zero]
      rw [show t+1-u=(t-u)+1 by omega,pow_succ,mul_comm]

lemma row_covariance_fin (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    (∑ k : Fin (n+1), row r t.val k.val*row r u.val k.val)=r^(t.val-u.val) := by
  rw [Fin.sum_univ_eq_sum_range (fun k => row r t.val k*row r u.val k)]
  exact row_covariance r hr hr1 n t.val u.val (by omega) hu

lemma one_sub_pow_le (r : ℝ) (hr : 0≤r) (hr1 : r≤1) (t : ℕ) :
    1-r^t ≤ t*(1-r) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [pow_succ,Nat.cast_add,Nat.cast_one]
    have hp : r^t≤1 := pow_le_one₀ hr hr1
    nlinarith

end GaussianAR

end

section

open Matrix
open scoped BigOperators RealInnerProductSpace
namespace GaussianTail
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
lemma trace_covariance (B : Matrix κ ι ℝ) : (B*B.transpose).trace=squareMass B := by
  simp only [Matrix.trace,Matrix.diag,Matrix.mul_apply,Matrix.transpose_apply,squareMass,← sq]

lemma squareMass_mul_covariance (B : Matrix κ ι ℝ) (C : Matrix ι ν ℝ) :
    squareMass (B*C) = (B*(C*C.transpose)*B.transpose).trace := by
  rw [← trace_covariance,Matrix.transpose_mul]
  congr 1
  simp only [Matrix.mul_assoc]

lemma squareMass_add_le (B C : Matrix κ ι ℝ) :
    squareMass (B+C) ≤ 2*squareMass B+2*squareMass C := by
  unfold squareMass
  simp only [Finset.mul_sum,← Finset.sum_add_distrib,Matrix.add_apply]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro k _
  nlinarith [sq_nonneg (B i k-C i k)]

lemma squareMass_neg (B : Matrix κ ι ℝ) : squareMass (-B)=squareMass B := by
  simp [squareMass]

end GaussianTail
namespace GaussianAR
open GaussianTail
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma evaluation_mul_transpose (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    evaluation r n t*(evaluation r n u).transpose = diagonal (fun i => (r i)^(t.val-u.val)) := by
  ext i j
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_prod_type,evaluation]
  by_cases hij : i=j
  · subst j
    simp only [mul_ite,ite_mul,mul_zero,zero_mul]
    simp only [Finset.sum_ite_eq,Finset.mem_univ,ite_true,Matrix.diagonal_apply_eq]
    exact row_covariance_fin (r i) (hr i) (hr1 i) n t u hu
  · rw [Matrix.diagonal_apply_ne _ hij]
    apply Finset.sum_eq_zero
    intro k _
    apply Finset.sum_eq_zero
    intro l _
    split_ifs <;> simp_all

lemma evaluation_coisometry (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t : Fin (n+1)) :
    evaluation r n t*(evaluation r n t).transpose=1 := by
  rw [evaluation_mul_transpose r hr hr1 n t t le_rfl]
  simp

lemma evaluation_cross_symmetric (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) :
    evaluation r n t*(evaluation r n u).transpose = evaluation r n u*(evaluation r n t).transpose := by
  rcases le_total u t with h|h
  · have ht : (evaluation r n t*(evaluation r n u).transpose).transpose =
        evaluation r n t*(evaluation r n u).transpose := by
      rw [evaluation_mul_transpose r hr hr1 n t u h,Matrix.diagonal_transpose]
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using ht.symm
  · have ht : (evaluation r n u*(evaluation r n t).transpose).transpose =
        evaluation r n u*(evaluation r n t).transpose := by
      rw [evaluation_mul_transpose r hr hr1 n u t h,Matrix.diagonal_transpose]
    simpa only [Matrix.transpose_mul,Matrix.transpose_transpose] using ht

lemma evaluation_difference_covariance (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (t u : Fin (n+1)) (hu : u≤t) :
    (evaluation r n t-evaluation r n u)*(evaluation r n t-evaluation r n u).transpose =
      diagonal (fun i => 2*(1-(r i)^(t.val-u.val))) := by
  rw [Matrix.transpose_sub,Matrix.mul_sub,Matrix.sub_mul,Matrix.sub_mul,
    evaluation_coisometry r hr hr1,evaluation_coisometry r hr hr1,
    ← evaluation_cross_symmetric r hr hr1 n t u,evaluation_mul_transpose r hr hr1 n t u hu]
  ext i j
  by_cases h : i=j
  · subst j; simp; ring
  · simp [h]

lemma squareMass_evaluation {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1) (n : ℕ) (t : Fin (n+1)) :
    squareMass (B*evaluation r n t)=squareMass B := by
  rw [squareMass_mul_covariance,evaluation_coisometry r hr hr1,Matrix.mul_one,trace_covariance]

lemma trace_weighted_square {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ) (w : ι → ℝ) :
    (B*diagonal w*B.transpose).trace = ∑ i,∑ j,(B i j)^2*w j := by
  change (∑ i,∑ j,(B*diagonal w) i j*B i j) = _
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma squareMass_time_le {κ : Type*} [Fintype κ] (B : Matrix κ ι ℝ)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1) (n : ℕ) (t u : Fin (n+1)) :
    squareMass (B*(evaluation r n t-evaluation r n u)) ≤
      2*|(t.val:ℝ)-u.val| * (B*diagonal (fun i => 1-r i)*B.transpose).trace := by
  wlog hu : u≤t generalizing t u
  · have h := this u t (le_of_not_ge hu)
    rw [show evaluation r n t-evaluation r n u= -(evaluation r n u-evaluation r n t) by abel,
      Matrix.mul_neg,squareMass_neg,abs_sub_comm]
    exact h
  rw [squareMass_mul_covariance,evaluation_difference_covariance r hr hr1 n t u hu,
    trace_weighted_square,trace_weighted_square,abs_of_nonneg (sub_nonneg.mpr (show (u.val:ℝ) ≤ t.val by exact_mod_cast hu)),
    ← Nat.cast_sub hu]
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h := one_sub_pow_le (r j) (hr j) (hr1 j) (t.val-u.val)
  nlinarith [mul_nonneg (sq_nonneg (B i j)) (sub_nonneg.mpr h)]

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Chaining
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian chaining, finite nets, and uniform process bounds. -/

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators
namespace GaussianChaining

lemma nat_add_one_le_two_pow (j : ℕ) : (j:ℝ)+1 ≤ (2:ℝ)^j := by
  exact_mod_cast j.lt_two_pow_self

lemma exponent_le (j l : ℕ) : (exponent j l : ℝ) ≤ 30*(2:ℝ)^j*(l+1) := by
  have hj := nat_add_one_le_two_pow j
  have h0 : (0:ℝ) ≤ j := Nat.cast_nonneg j
  have h1 : (0:ℝ) ≤ l := Nat.cast_nonneg l
  have hp : 0 ≤ (j:ℝ)*l := mul_nonneg h0 h1
  calc
    _ ≤ 30*((j:ℝ)+1)*(l+1) := by simp only [exponent,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]; nlinarith
    _ ≤ _ := by gcongr

lemma radius_nonneg {A : ℝ} (hA : 0 ≤ A) (j l : ℕ) : 0 ≤ radius A j l := by
  unfold radius
  positivity

lemma tail_threshold_le {A : ℝ} (hA : 1 ≤ A) (j l : ℕ) :
    2*variance A j l+8*Real.sqrt (variance A j l)*(exponent j l) ≤ (radius A j l)^2 := by
  let p : ℝ := (2:ℝ)^j
  let z : ℝ := (1/2:ℝ)^l
  let m : ℝ := l+1
  have hp : 0 ≤ p := by dsimp [p]; positivity
  have hz : 0 ≤ z := by dsimp [z]; positivity
  have hz1 : z ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hz2 : z^2 ≤ 1 := by nlinarith
  have hm : 1 ≤ m := by dsimp [m]; have := Nat.cast_nonneg (α := ℝ) l; linarith
  have hs : Real.sqrt (variance A j l) = Real.sqrt A*p*z^2 := by
    unfold variance
    rw [Real.sqrt_mul (mul_nonneg (by linarith) (sq_nonneg _)),Real.sqrt_mul (by linarith : 0 ≤ A)]
    rw [Real.sqrt_sq hp,show (((1/2:ℝ)^l)^4) = (((1/2:ℝ)^l)^2)^2 by ring,
      Real.sqrt_sq (sq_nonneg _)]
  have hr : (exponent j l : ℝ) ≤ 30*p*m := exponent_le j l
  have ha : 0 ≤ A := by linarith
  have hsa : Real.sqrt A ≤ A+1 := by
    have := Real.sq_sqrt ha
    have := Real.sqrt_nonneg A
    nlinarith [sq_nonneg (A-1)]
  have hc : 2*A+240*Real.sqrt A*m ≤ (100*(A+1)*m)^2 := by
    calc
      _ ≤ 2*(A+1)*m^2+240*(A+1)*m^2 := by
        apply add_le_add
        · have hm2 : 1 ≤ m^2 := by nlinarith
          nlinarith [mul_nonneg (by linarith : 0 ≤ A+1) (sub_nonneg.mpr hm2)]
        · have hm2 : m ≤ m^2 := by nlinarith
          exact (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsa (by norm_num)) (by linarith)).trans
            (mul_le_mul_of_nonneg_left hm2 (by positivity))
      _ ≤ _ := by
        have h : 242*(A+1) ≤ 10000*(A+1)^2 := by nlinarith [sq_nonneg (A+1)]
        nlinarith [mul_nonneg (sub_nonneg.mpr h) (sq_nonneg m)]
  rw [hs]
  calc
    _ ≤ 2*(A*p^2*z^4)+8*(Real.sqrt A*p*z^2)*(30*p*m) := by
      unfold variance
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hr (by positivity))
    _ ≤ (2*A+240*Real.sqrt A*m)*(p*z)^2 := by
      have hh : A*p^2*z^2*z^2 ≤ A*p^2*z^2 :=
        mul_le_of_le_one_right (by positivity) hz2
      nlinarith
    _ ≤ (100*(A+1)*m)^2*(p*z)^2 := mul_le_mul_of_nonneg_right hc (sq_nonneg _)
    _ = _ := by dsimp [radius,p,z,m]; ring

lemma exp_exponent_le (j l : ℕ) :
    Real.exp (-(exponent j l : ℝ)) ≤ (1/2:ℝ)^(exponent j l) := by
  rw [show -(exponent j l : ℝ) = (exponent j l : ℝ)*(-1) by ring,Real.exp_nat_mul]
  apply pow_le_pow_left₀ (Real.exp_pos _).le
  have h : (2:ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1:ℝ); linarith
  rw [Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

lemma edge_failure (B : Matrix κ ι ℝ) {A : ℝ} (hA : 1 ≤ A) (j l : ℕ)
    (hS : GaussianTail.squareMass B ≤ variance A j l)
    (hB : ∀ x : EuclideanSpace ℝ ι, ‖GaussianTail.matrixMap B x‖^2 ≤ 4*‖x‖^2) :
    stdGaussian (EuclideanSpace ℝ ι) {x | radius A j l < ‖GaussianTail.matrixMap B x‖} ≤
      ENNReal.ofReal ((1/2:ℝ)^(exponent j l)) := by
  apply le_trans (measure_mono (show {x | radius A j l < ‖GaussianTail.matrixMap B x‖} ⊆
    {x | 2*variance A j l+8*Real.sqrt (variance A j l)*(exponent j l) ≤
      ‖GaussianTail.matrixMap B x‖^2} from ?_))
    ((GaussianTail.interpolated_tail B (by unfold variance; positivity) hS hB _).trans
      (ENNReal.ofReal_le_ofReal (exp_exponent_le j l)))
  intro x hx
  have hn := norm_nonneg (GaussianTail.matrixMap B x)
  have hr := radius_nonneg (by linarith : 0 ≤ A) j l
  have ht := tail_threshold_le hA j l
  change radius A j l < ‖GaussianTail.matrixMap B x‖ at hx
  change 2*variance A j l+8*Real.sqrt (variance A j l)*(exponent j l) ≤ _
  nlinarith

lemma entropy_weight (j l : ℕ) :
    (2:ℝ≥0∞)^(24*(l+1)) * (1/2:ℝ≥0∞)^(exponent j l) =
      (1/2:ℝ≥0∞)^(j+l+5) := by
  rw [show exponent j l = 24*(l+1)+(j+l+5) by simp [exponent]; omega,pow_add,← mul_assoc,← mul_pow]
  norm_num only [one_div]
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_pow,one_mul]

lemma weight_sum (j : ℕ) :
    (∑' l : ℕ, (1/2:ℝ≥0∞)^(j+l+5)) = (1/2:ℝ≥0∞)^(j+4) := by
  have he (l : ℕ) : j+l+5 = (j+4)+(l+1) := by omega
  simp only [he,pow_add,pow_succ]
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
  norm_num only [one_div,inv_inv]
  norm_num
  rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),mul_one]

lemma weight_sum_all : (∑' j : ℕ, (1/2:ℝ≥0∞)^(j+4)) = 1/8 := by
  simp only [pow_add]
  rw [ENNReal.tsum_mul_right,ENNReal.tsum_geometric]
  norm_num
  calc
    _ = ((2:ℝ≥0∞)*2⁻¹)*(2⁻¹)^3 := by ring
    _ = _ := by rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num),one_mul,← ENNReal.inv_pow]; norm_num

lemma level_failure (S : Finset (Matrix κ ι ℝ)) {A : ℝ} (hA : 1 ≤ A) (j l : ℕ)
    (hcard : S.card ≤ 2^(24*(l+1)))
    (hS : ∀ B ∈ S, GaussianTail.squareMass B ≤ variance A j l)
    (hB : ∀ B ∈ S, ∀ x : EuclideanSpace ℝ ι, ‖GaussianTail.matrixMap B x‖^2 ≤ 4*‖x‖^2) :
    stdGaussian (EuclideanSpace ℝ ι) (⋃ B ∈ S, {x | radius A j l < ‖GaussianTail.matrixMap B x‖}) ≤
      (1/2:ℝ≥0∞)^(j+l+5) := by
  calc
    _ ≤ ∑ B ∈ S, stdGaussian (EuclideanSpace ℝ ι) {x | radius A j l < ‖GaussianTail.matrixMap B x‖} :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _B ∈ S, ENNReal.ofReal ((1/2:ℝ)^(exponent j l)) :=
      Finset.sum_le_sum fun B h => edge_failure B hA j l (hS B h) (hB B h)
    _ = (S.card:ℝ≥0∞)*(1/2:ℝ≥0∞)^(exponent j l) := by
      simp [ENNReal.ofReal_pow,ENNReal.inv_pow]
    _ ≤ (2:ℝ≥0∞)^(24*(l+1))*(1/2:ℝ≥0∞)^(exponent j l) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := entropy_weight j l

lemma radius_sum (A : ℝ) (j : ℕ) :
    (∑' l : ℕ, radius A j l) = 400*(A+1)*(2:ℝ)^j := by
  have he (l : ℕ) : radius A j l = (100*(A+1)*(2:ℝ)^j)*((l+1)*(1/2:ℝ)^l) := by
    dsimp [radius]; ring
  simp only [he]
  rw [tsum_mul_left]
  have hs : (∑' l : ℕ, ((l:ℝ)+1)*(1/2:ℝ)^l) = 4 := by
    have h1 := hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)
    have h2 := hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)
    have ht := (h1.add h2).tsum_eq
    norm_num at ht
    simpa only [add_mul,one_mul] using ht
  rw [hs]
  ring

end GaussianChaining

end

section

open Filter
open scoped Topology BigOperators
namespace GridNets

lemma cell_le (l : ℕ) {a : ℝ} (ha : a ≤ 1) : cell l a ≤ 64^l := by
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_right (by positivity) ha

lemma cellPair_mem {k l : ℕ} (hkl : k ≤ l) {p : ℝ × ℝ} (hp : InSquare p) :
    cellPair k p ∈ grid l := by
  have hn : 64^k ≤ 64^l := Nat.pow_le_pow_right (by norm_num) hkl
  simp only [grid,cellPair,Finset.mem_product,Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le ((cell_le k hp.2.1).trans hn),
    Nat.lt_succ_of_le ((cell_le k hp.2.2.2).trans hn)⟩

lemma abs_sub_lt_width (l : ℕ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : cell l a = cell l b) : |a-b| < (1/64:ℝ)^l := by
  have hp : 0 < (64:ℝ)^l := by positivity
  have hfa := Nat.floor_le (mul_nonneg hp.le ha)
  have hfb := Nat.floor_le (mul_nonneg hp.le hb)
  have hga := Nat.lt_floor_add_one ((64:ℝ)^l*a)
  have hgb := Nat.lt_floor_add_one ((64:ℝ)^l*b)
  change ⌊(64:ℝ)^l*a⌋₊ = ⌊(64:ℝ)^l*b⌋₊ at h
  rw [h] at hfa hga
  rw [div_pow,one_pow,abs_lt]
  constructor
  · have hh : b-a < 1/(64:ℝ)^l := (lt_div_iff₀ hp).mpr (by nlinarith)
    linarith
  · apply (lt_div_iff₀ hp).mpr
    nlinarith

lemma eventually_cell_separates {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ∀ᶠ l : ℕ in atTop, cell l a = cell l b → a = b := by
  by_cases hab : a = b
  · exact Eventually.of_forall fun _ _ => hab
  · have hp : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
    have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/64)
      (by norm_num : (1/64:ℝ)<1)
    filter_upwards [hlim.eventually (gt_mem_nhds hp)] with l hl he
    exact False.elim ((not_lt_of_ge (le_of_lt hl)) (abs_sub_lt_width l ha hb he))

variable {I : Type*} [Fintype I] [Nonempty I]

lemma rep_cell (p : I → ℝ × ℝ) (l : ℕ) (i : I) :
    cellPair l (p (rep p l i)) = cellPair l (p i) := by
  dsimp [rep,point]
  rw [dite_eq_left ⟨i,rfl⟩]
  exact Classical.choose_spec (show ∃ k, cellPair l (p k) = cellPair l (p i) from ⟨i,rfl⟩)

lemma rep_distance (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) (i : I) :
    |(p (rep p l i)).1-(p i).1| < (1/64:ℝ)^l ∧
    |(p (rep p l i)).2-(p i).2| < (1/64:ℝ)^l := by
  have he := rep_cell p l i
  exact ⟨abs_sub_lt_width l (hp _).1 (hp _).1 (congrArg Prod.fst he),
    abs_sub_lt_width l (hp _).2.2.1 (hp _).2.2.1 (congrArg Prod.snd he)⟩

lemma eventually_rep_eq (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) :
    ∀ᶠ l : ℕ in atTop, ∀ i, p (rep p l i) = p i := by
  have hall : ∀ᶠ l : ℕ in atTop, ∀ i k, cellPair l (p i) = cellPair l (p k) → p i = p k := by
    apply eventually_all.mpr
    intro i
    apply eventually_all.mpr
    intro k
    filter_upwards [eventually_cell_separates (hp i).1 (hp k).1,
      eventually_cell_separates (hp i).2.2.1 (hp k).2.2.1] with l h1 h2 h
    exact Prod.ext (h1 (congrArg Prod.fst h)) (h2 (congrArg Prod.snd h))
  filter_upwards [hall] with l hl i
  exact hl _ _ (rep_cell p l i)

lemma grid_card (l : ℕ) : (grid l).card = (64^l+1)^2 := by simp [grid,pow_two]

lemma grid_card_square_le (l : ℕ) : (grid l).card^2 ≤ 2^(24*(l+1)) := by
  rw [grid_card]
  have hp : 1 ≤ 64^l := Nat.one_le_pow l 64 (by norm_num)
  calc
    ((64^l+1)^2)^2 ≤ ((2*64^l)^2)^2 := by gcongr; omega
    _ = 2^(24*l+4) := by
      rw [← pow_mul, mul_pow, show (64:ℕ)=2^6 by norm_num,← pow_mul,← pow_mul,← pow_add]
      congr 1
      omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)

lemma image_pair_card_le {α : Type*} [DecidableEq α] (p : I → ℝ × ℝ)
    (hp : ∀ i, InSquare (p i)) (l : ℕ) (f : I → I → α) :
    (Finset.univ.image (fun i => f (rep p l i) (rep p (l-1) i))).card ≤ 2^(24*(l+1)) := by
  classical
  have hs : Finset.univ.image (fun i => f (rep p l i) (rep p (l-1) i)) ⊆
      (grid l ×ˢ grid l).image (fun c => f (point p l c.1) (point p (l-1) c.2)) := by
    intro a ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_image.mpr ⟨(cellPair l (p i),cellPair (l-1) (p i)),
      Finset.mem_product.mpr ⟨cellPair_mem le_rfl (hp i),cellPair_mem (Nat.sub_le _ _) (hp i)⟩,rfl⟩
  exact ((Finset.card_le_card hs).trans Finset.card_image_le).trans (by
    simpa only [Finset.card_product,pow_two] using grid_card_square_le l)

end GridNets

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal BigOperators Topology
namespace GaussianTail
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]

omit [DecidableEq ι] in
lemma squareMass_eq_zero {B : Matrix κ ι ℝ} (h : squareMass B = 0) : B = 0 := by
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ =>
    Finset.sum_nonneg (fun k _ => sq_nonneg (B i k)))).mp h
  ext i k
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => sq_nonneg (B i k))).mp (h1 i (by simp)) k (by simp)
  simpa only [sq_eq_zero_iff,Matrix.zero_apply] using h2

lemma difference_operator (B C : Matrix κ ι ℝ)
    (hB : ∀ x : EuclideanSpace ℝ ι, ‖matrixMap B x‖^2 ≤ ‖x‖^2)
    (hC : ∀ x : EuclideanSpace ℝ ι, ‖matrixMap C x‖^2 ≤ ‖x‖^2) :
    ∀ x : EuclideanSpace ℝ ι, ‖matrixMap (B-C) x‖^2 ≤ 4*‖x‖^2 := by
  intro x
  have hb : ‖matrixMap B x‖ ≤ ‖x‖ := by nlinarith [hB x,norm_nonneg x,norm_nonneg (matrixMap B x)]
  have hc : ‖matrixMap C x‖ ≤ ‖x‖ := by nlinarith [hC x,norm_nonneg x,norm_nonneg (matrixMap C x)]
  rw [matrixMap_sub]
  have h := norm_sub_le (matrixMap B x) (matrixMap C x)
  have h0 := norm_nonneg (matrixMap B x-matrixMap C x)
  nlinarith
end GaussianTail

namespace GaussianChaining
open GaussianTail GridNets

lemma width_power (n : ℕ) : ((1/64:ℝ)^n)^(2/3:ℝ) = ((1/2:ℝ)^n)^4 := by
  rw [show (1/64:ℝ)=(1/2)^6 by norm_num,← pow_mul,← Real.rpow_natCast,← Real.rpow_mul (by norm_num),
    ← pow_mul,← Real.rpow_natCast]
  congr 1
  push_cast
  ring

lemma coordinate_power_bound (n : ℕ) {a : ℝ} (ha : 0 ≤ a) (hab : a ≤ 2*(1/64:ℝ)^n) :
    a^(2/3:ℝ) ≤ 2*((1/2:ℝ)^n)^4 := by
  have h2 : (2:ℝ)^(2/3:ℝ) ≤ 2 := by
    simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) (by norm_num : (2/3:ℝ)≤1)
  calc
    _ ≤ (2*(1/64:ℝ)^n)^(2/3:ℝ) := Real.rpow_le_rpow ha hab (by norm_num)
    _ = (2:ℝ)^(2/3:ℝ)*((1/2:ℝ)^n)^4 := by rw [Real.mul_rpow (by norm_num) (by positivity),width_power]
    _ ≤ _ := mul_le_mul_of_nonneg_right h2 (by positivity)

lemma width_le_quarter (n : ℕ) : (1/64:ℝ)^n ≤ ((1/2:ℝ)^n)^4 := by
  rw [← pow_mul, mul_comm n 4,pow_mul]
  apply pow_le_pow_left₀ (by norm_num)
  norm_num

variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I] [Nonempty I]

omit [DecidableEq ι] in
lemma edgeSet_card (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) :
    (edgeSet B p l).card ≤ 2^(24*(l+1)) := by
  classical
  cases l with
  | zero => exact image_pair_card_le p hp 0 (fun i _ => B i)
  | succ l =>
      change (Finset.univ.image (fun i => B (rep p (l+1) i)-B (rep p l i))).card ≤ _
      simpa only [Nat.add_sub_cancel] using image_pair_card_le p hp (l+1) (fun i k => B i-B k)

lemma adjacent_distance (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i)) (l : ℕ) (i : I) :
    |(p (rep p (l+1) i)).1-(p (rep p l i)).1| ≤ 2*(1/64:ℝ)^l ∧
    |(p (rep p (l+1) i)).2-(p (rep p l i)).2| ≤ 2*(1/64:ℝ)^l := by
  have h1 := rep_distance p hp (l+1) i
  have h2 := rep_distance p hp l i
  have hw : (1/64:ℝ)^(l+1) ≤ (1/64:ℝ)^l := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (by positivity) (by norm_num)
  constructor
  · have ht := abs_sub_le (p (rep p (l+1) i)).1 (p i).1 (p (rep p l i)).1
    rw [abs_sub_comm (p i).1] at ht
    linarith [h1.1,h2.1]
  · have ht := abs_sub_le (p (rep p (l+1) i)).2 (p i).2 (p (rep p l i)).2
    rw [abs_sub_comm (p i).2] at ht
    linarith [h1.2,h2.2]

omit [DecidableEq ι] in
lemma netEdge_variance (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hbase : ∀ i, squareMass (B i) ≤ C*((2:ℝ)^j)^2)
    (hdiff : ∀ i k, squareMass (B i-B k) ≤ C*((2:ℝ)^j)^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|))
    (l : ℕ) (i : I) : squareMass (netEdge B p l i) ≤ variance (64*C+1) j l := by
  cases l with
  | zero =>
    apply (hbase _).trans
    dsimp [variance]
    simp only [pow_zero,one_pow,mul_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)
  | succ l =>
    have hd := adjacent_distance p hp l i
    have hh : |(p (rep p (l+1) i)).1-(p (rep p l i)).1|^(2/3:ℝ)+
        |(p (rep p (l+1) i)).2-(p (rep p l i)).2| ≤ 4*((1/2:ℝ)^l)^4 := by
      have h1 := coordinate_power_bound l (abs_nonneg _) hd.1
      have h2 := width_le_quarter l
      linarith [hd.2]
    calc
      _ ≤ C*((2:ℝ)^j)^2*(|(p (rep p (l+1) i)).1-(p (rep p l i)).1|^(2/3:ℝ)+
        |(p (rep p (l+1) i)).2-(p (rep p l i)).2|) := hdiff _ _
      _ ≤ C*((2:ℝ)^j)^2*(4*((1/2:ℝ)^l)^4) := mul_le_mul_of_nonneg_left hh (by positivity)
      _ ≤ variance (64*C+1) j (l+1) := by
        dsimp [variance]
        rw [pow_succ (1/2:ℝ) l]
        have hn : 0 ≤ ((2:ℝ)^j)^2*((1/2:ℝ)^l)^4 := by positivity
        nlinarith

lemma netEdge_operator (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ)
    (hop : ∀ i x, ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2) (l : ℕ) (i : I) :
    ∀ x, ‖matrixMap (netEdge B p l i) x‖^2 ≤ 4*‖x‖^2 := by
  cases l with
  | zero => intro x; exact (hop _ x).trans (by nlinarith [sq_nonneg ‖x‖])
  | succ l => exact difference_operator _ _ (hop _) (hop _)

omit [Fintype ι] [DecidableEq ι] [Fintype κ] in
lemma netEdge_sum (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (i : I) (n : ℕ) :
    ∑ l ∈ Finset.range (n+1), netEdge B p l i = netEnd B p n i := by
  induction n with
  | zero => simp [netEdge]
  | succ n ih => rw [Finset.sum_range_succ,ih,netEdge]; abel

omit [DecidableEq ι] in
lemma eventually_netEnd_eq (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    {C : ℝ} (j : ℕ) (hdiff : ∀ i k, squareMass (B i-B k) ≤ C*((2:ℝ)^j)^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|)) :
    ∀ᶠ l : ℕ in atTop, ∀ i, netEnd B p l i = B i := by
  filter_upwards [eventually_rep_eq p hp] with l hl i
  apply sub_eq_zero.mp
  apply squareMass_eq_zero
  apply le_antisymm _ (squareMass_nonneg _)
  have h := hdiff (rep p l i) i
  simpa only [netEnd,hl i, sub_self,abs_zero,Real.zero_rpow (by norm_num : (2/3:ℝ)≠0),add_zero,mul_zero] using h

lemma radius_summable (A : ℝ) (j : ℕ) : Summable (fun l : ℕ => radius A j l) := by
  have h1 := (hasSum_coe_mul_geometric_of_norm_lt_one (r := (1/2:ℝ)) (by norm_num)).summable
  have h2 := (hasSum_geometric_of_norm_lt_one (ξ := (1/2:ℝ)) (by norm_num)).summable
  have h := (h1.add h2).mul_left (100*(A+1)*(2:ℝ)^j)
  apply h.congr
  intro l
  dsimp [radius]
  ring

lemma netEnd_norm_le (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) {A : ℝ} (hA : 0 ≤ A) (j : ℕ)
    (x : EuclideanSpace ℝ ι)
    (h : ∀ l i, ‖matrixMap (netEdge B p l i) x‖ ≤ radius A j l) (n : ℕ) (i : I) :
    ‖matrixMap (netEnd B p n i) x‖ ≤ 400*(A+1)*(2:ℝ)^j := by
  have hs : matrixMap (netEnd B p n i) x =
      ∑ l ∈ Finset.range (n+1), matrixMap (netEdge B p l i) x := by
    rw [← netEdge_sum B p i n]
    simp only [matrixMap, map_sum, _root_.sum_apply]
  rw [hs]
  calc
    _ ≤ ∑ l ∈ Finset.range (n+1), ‖matrixMap (netEdge B p l i) x‖ := norm_sum_le _ _
    _ ≤ ∑ l ∈ Finset.range (n+1), radius A j l := Finset.sum_le_sum fun l _ => h l i
    _ ≤ ∑' l, radius A j l := (radius_summable A j).sum_le_tsum _ (fun l _ => radius_nonneg hA j l)
    _ = _ := radius_sum A j

lemma class_failure (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    {C : ℝ} (hC : 0 ≤ C) (j : ℕ)
    (hbase : ∀ i, squareMass (B i) ≤ C*((2:ℝ)^j)^2)
    (hdiff : ∀ i k, squareMass (B i-B k) ≤ C*((2:ℝ)^j)^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|))
    (hop : ∀ i x, ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2) :
    stdGaussian (EuclideanSpace ℝ ι) {x | ∃ i,400*(64*C+2)*(2:ℝ)^j < ‖matrixMap (B i) x‖} ≤
      (1/2:ℝ≥0∞)^(j+4) := by
  have hA : 1 ≤ 64*C+1 := by linarith
  have hsub : {x | ∃ i,400*(64*C+2)*(2:ℝ)^j < ‖matrixMap (B i) x‖} ⊆
      ⋃ l, ⋃ D ∈ edgeSet B p l, {x | radius (64*C+1) j l < ‖matrixMap D x‖} := by
    intro x hx
    by_contra hbad
    have he : ∀ l i, ‖matrixMap (netEdge B p l i) x‖ ≤ radius (64*C+1) j l := by
      intro l i
      apply le_of_not_gt
      intro hg
      apply hbad
      simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
      refine ⟨l,netEdge B p l i,?_,hg⟩
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    obtain ⟨n,hn⟩ := (eventually_netEnd_eq B p hp j hdiff).exists
    obtain ⟨i,hi⟩ := hx
    have hb := netEnd_norm_le B p (by linarith : 0 ≤ 64*C+1) j x he n i
    rw [hn i] at hb
    have hconst : 64*C+1+1=64*C+2 := by ring
    rw [hconst] at hb
    exact not_lt_of_ge hb hi
  apply (measure_mono hsub).trans
  calc
    _ ≤ ∑' l : ℕ, (1/2:ℝ≥0∞)^(j+l+5) := by
      apply (measure_iUnion_le _).trans
      apply ENNReal.tsum_le_tsum
      intro l
      apply level_failure (edgeSet B p l) hA j l (edgeSet_card B p hp l)
      · intro D hD
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hD
        exact netEdge_variance B p hp hC j hbase hdiff l i
      · intro D hD
        obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hD
        exact netEdge_operator B p hop l i
    _ = _ := weight_sum j

end GaussianChaining

end

section

open Matrix
open scoped RealInnerProductSpace
namespace GaussianTail
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq ν]

omit [DecidableEq κ] in
lemma matrixMap_mul (B : Matrix κ ι ℝ) (C : Matrix ι ν ℝ) (x : EuclideanSpace ℝ ν) :
    matrixMap (B*C) x=matrixMap B (matrixMap C x) := by
  apply WithLp.ofLp_injective
  exact (Matrix.mulVec_mulVec (WithLp.ofLp x) B C).symm

lemma inner_matrixMap (B : Matrix κ ι ℝ) (x : EuclideanSpace ℝ ι) (y : EuclideanSpace ℝ κ) :
    ⟪matrixMap B x,y⟫=⟪x,matrixMap B.transpose y⟫ := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, star_trivial]
  change y.ofLp ⬝ᵥ (B.mulVec x.ofLp) = (B.transpose.mulVec y.ofLp) ⬝ᵥ x.ofLp
  rw [Matrix.dotProduct_mulVec,Matrix.mulVec_transpose]

lemma coisometry_operator (B : Matrix κ ι ℝ) (hB : B*B.transpose=1) :
    ∀ x : EuclideanSpace ℝ ι, ‖matrixMap B x‖^2 ≤ ‖x‖^2 := by
  intro x
  have ht : ∀ y : EuclideanSpace ℝ κ, ‖matrixMap B.transpose y‖=‖y‖ := by
    intro y
    have hh := gram_form B.transpose y
    rw [Matrix.transpose_transpose,hB] at hh
    have he : toEuclideanCLM (𝕜 := ℝ) (1 : Matrix κ κ ℝ) y=y := by
      apply WithLp.ofLp_injective
      exact Matrix.one_mulVec _
    rw [he,real_inner_self_eq_norm_sq] at hh
    nlinarith [norm_nonneg (matrixMap B.transpose y),norm_nonneg y]
  have hi := real_inner_le_norm (x := x) (y := matrixMap B.transpose (matrixMap B x))
  rw [← inner_matrixMap,real_inner_self_eq_norm_sq,ht] at hi
  have hn : ‖matrixMap B x‖ ≤ ‖x‖ := by
    nlinarith [norm_nonneg (matrixMap B x),norm_nonneg x]
  nlinarith [norm_nonneg (matrixMap B x),norm_nonneg x]

end GaussianTail

end

section

open Matrix MeasureTheory ProbabilityTheory Filter
open scoped RealInnerProductSpace ENNReal NNReal BigOperators Topology
namespace GaussianChaining
open GaussianTail GridNets
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I]

lemma classified_failure (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    (J : I → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbase : ∀ i, squareMass (B i) ≤ C*((2:ℝ)^(J i))^2)
    (hdiff : ∀ i k, J i=J k → squareMass (B i-B k) ≤ C*((2:ℝ)^(J i))^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|))
    (hop : ∀ i x, ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2) :
    stdGaussian (EuclideanSpace ℝ ι) {x | ∃ i,400*(64*C+2)*(2:ℝ)^(J i) < ‖matrixMap (B i) x‖} ≤
      1/8 := by
  classical
  have hj (j : ℕ) : stdGaussian (EuclideanSpace ℝ ι)
      {x | ∃ i, J i=j ∧ 400*(64*C+2)*(2:ℝ)^j < ‖matrixMap (B i) x‖} ≤ (1/2:ℝ≥0∞)^(j+4) := by
    by_cases h : Nonempty {i // J i=j}
    · let := h
      have hh := class_failure (fun i : {i // J i=j} => B i) (fun i => p i)
        (fun i => hp i) hC j
        (fun i => by simpa only [i.property] using hbase i)
        (fun i k => by simpa only [i.property] using hdiff i k (i.property.trans k.property.symm))
        (fun i => hop i)
      convert hh using 1
      congr 1
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨i,hi,hh⟩; exact ⟨⟨i,hi⟩,hh⟩
      · rintro ⟨⟨i,hi⟩,hh⟩; exact ⟨i,hi,hh⟩
    · have he : {x : EuclideanSpace ℝ ι | ∃ i, J i=j ∧ 400*(64*C+2)*(2:ℝ)^j < ‖matrixMap (B i) x‖} = ∅ := by
        ext x
        simp only [Set.mem_ofPred_eq,Set.mem_empty_iff_false,iff_false]
        rintro ⟨i,hi,_⟩
        exact h ⟨⟨i,hi⟩⟩
      rw [he,measure_empty]
      positivity
  have hs : {x | ∃ i,400*(64*C+2)*(2:ℝ)^(J i) < ‖matrixMap (B i) x‖} ⊆
      ⋃ j : ℕ, {x | ∃ i, J i=j ∧ 400*(64*C+2)*(2:ℝ)^j < ‖matrixMap (B i) x‖} := by
    rintro x ⟨i,hi⟩
    exact Set.mem_iUnion.mpr ⟨J i,i,rfl,hi⟩
  apply (measure_mono hs).trans
  apply (measure_iUnion_le _).trans
  exact (ENNReal.tsum_le_tsum hj).trans_eq weight_sum_all

lemma classified_survival (B : I → Matrix κ ι ℝ) (p : I → ℝ × ℝ) (hp : ∀ i, InSquare (p i))
    (J : I → ℕ) {C : ℝ} (hC : 0 ≤ C)
    (hbase : ∀ i, squareMass (B i) ≤ C*((2:ℝ)^(J i))^2)
    (hdiff : ∀ i k, J i=J k → squareMass (B i-B k) ≤ C*((2:ℝ)^(J i))^2*
      (|(p i).1-(p k).1|^(2/3:ℝ)+|(p i).2-(p k).2|))
    (hop : ∀ i x, ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2) :
    (1/2:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ ι)
      {x | ∀ i, ‖matrixMap (B i) x‖ ≤ 400*(64*C+2)*(2:ℝ)^(J i)} := by
  let S := {x : EuclideanSpace ℝ ι | ∀ i, ‖matrixMap (B i) x‖ ≤ 400*(64*C+2)*(2:ℝ)^(J i)}
  have hm : MeasurableSet S := by
    simp only [S,Set.ofPred_forall]
    exact MeasurableSet.iInter fun i =>
      measurableSet_le (matrixMap (B i)).continuous.norm.measurable measurable_const
  have hc : Sᶜ = {x | ∃ i,400*(64*C+2)*(2:ℝ)^(J i) < ‖matrixMap (B i) x‖} := by
    ext x; simp [S,not_forall]
  have hf := classified_failure B p hp J hC hbase hdiff hop
  rw [← hc,measure_compl hm (measure_ne_top _ _),measure_univ] at hf
  have ht : (1:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ ι) S + 1/8 := by
    exact tsub_le_iff_left.mp hf
  have hn : (1/2:ℝ≥0∞)+1/8 ≤ 1 := by
    apply (ENNReal.toReal_le_toReal (by finiteness) (by finiteness)).mp
    rw [ENNReal.toReal_add (by finiteness) (by finiteness)]
    norm_num
  change (1/2:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ ι) S
  exact (ENNReal.add_le_add_iff_right (by norm_num : (1/8:ℝ≥0∞)≠⊤)).mp (hn.trans ht)

lemma sizeClass_bounds {k : ℝ} (hk : 1/4 ≤ k) :
    ((2:ℝ)^(sizeClass k))^2 ≤ 4*k ∧ k < ((2:ℝ)^(sizeClass k))^2 := by
  unfold sizeClass
  rw [dite_eq_left hk]
  set j := (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose
  have hj := (exists_nat_pow_near (by linarith : (1:ℝ) ≤ 4*k) (by norm_num : (1:ℝ)<4)).choose_spec
  change (4:ℝ)^j ≤ 4*k ∧ 4*k < 4^(j+1) at hj
  have he : ((2:ℝ)^j)^2 = 4^j := by rw [← pow_mul,mul_comm j 2,pow_mul]; norm_num
  rw [he]
  constructor
  · exact hj.1
  · rw [pow_succ] at hj; linarith [hj.2]

lemma sizeClass_sqrt {k : ℝ} (hk : 1/4 ≤ k) :
    (2:ℝ)^(sizeClass k) ≤ 2*Real.sqrt k := by
  have hs := Real.sq_sqrt (by linarith : 0 ≤ k)
  have hh := (sizeClass_bounds hk).1
  have h0 := Real.sqrt_nonneg k
  have hp : (0:ℝ) ≤ 2^(sizeClass k) := by positivity
  nlinarith

end GaussianChaining

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators
namespace GaussianAR
open GaussianTail GaussianChaining
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
  [Fintype I]

omit [DecidableEq κ] in
lemma block_survival (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (F : I → Matrix κ ι ℝ) (t : I → Fin (n+1))
    (a b k : I → ℝ) (ha : ∀ i,a i ∈ Set.Icc (0:ℝ) 1) (hb : ∀ i,b i ∈ Set.Icc (0:ℝ) 1)
    (hk : ∀ i,1/4 ≤ k i) {C θ : ℝ} (hC : 0 ≤ C)
    (hs : ∀ i,squareMass (F i) ≤ C*k i)
    (hi : ∀ i j, squareMass (F i-F j) ≤ C*(1+k i+k j)*|a i-a j|^(2/3:ℝ))
    (ht : ∀ i,(F i*diagonal (fun j => 1-r j)*(F i).transpose).trace ≤ C*k i*θ)
    (hbtime : ∀ i j, θ*|((t i).val:ℝ)-(t j).val| ≤ |b i-b j|)
    (hop : ∀ i x,‖matrixMap (F i) x‖^2 ≤ ‖x‖^2) :
    (1/2:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))
      {x | ∀ i, ‖matrixMap (F i*evaluation r n (t i)) x‖ ≤
        800*(640*C+2)*Real.sqrt (k i)} := by
  let B i := F i*evaluation r n (t i)
  let J i := sizeClass (k i)
  have hJ (i) : k i < ((2:ℝ)^(J i))^2 := (sizeClass_bounds (hk i)).2
  have hJ1 (i) : (1:ℝ) ≤ ((2:ℝ)^(J i))^2 := by
    exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hbase (i) : squareMass (B i) ≤ (10*C)*((2:ℝ)^(J i))^2 := by
    dsimp [B]
    rw [squareMass_evaluation _ r hr hr1]
    have hh := mul_le_mul_of_nonneg_left (hJ i).le hC
    have hn : 0 ≤ C*((2:ℝ)^(J i))^2 := by positivity
    linarith [hs i]
  have hd (i j) (hij : J i=J j) : squareMass (B i-B j) ≤
      (10*C)*((2:ℝ)^(J i))^2*(|a i-a j|^(2/3:ℝ)+|b i-b j|) := by
    have he : B i-B j=(F i-F j)*evaluation r n (t i)+
        F j*(evaluation r n (t i)-evaluation r n (t j)) := by
      dsimp [B]; rw [Matrix.sub_mul,Matrix.mul_sub]; abel
    rw [he]
    apply (squareMass_add_le _ _).trans
    rw [squareMass_evaluation _ r hr hr1]
    have hti := squareMass_time_le (F j) r hr hr1 n (t i) (t j)
    have hmul := mul_le_mul_of_nonneg_left (ht j) (by positivity : 0 ≤ 2*|((t i).val:ℝ)-(t j).val|)
    have hk0 : 0 ≤ k j := le_trans (by norm_num) (hk j)
    have hbt := mul_le_mul_of_nonneg_left (hbtime i j) (by positivity : 0 ≤ 2*C*k j)
    have htime : squareMass (F j*(evaluation r n (t i)-evaluation r n (t j))) ≤
        2*C*k j*|b i-b j| := by
      nlinarith [hti]
    have hjval : k j < ((2:ℝ)^(J i))^2 := by rw [hij]; exact hJ j
    have hh0 : C*(1+k i+k j) ≤ 3*C*((2:ℝ)^(J i))^2 := by
      nlinarith [mul_nonneg hC (sub_nonneg.mpr (hJ1 i)),
        mul_nonneg hC (sub_nonneg.mpr (hJ i).le),mul_nonneg hC (sub_nonneg.mpr hjval.le)]
    have hh := mul_le_mul_of_nonneg_right hh0 (by positivity : 0 ≤ |a i-a j|^(2/3:ℝ))
    have hh1 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hjval.le (by positivity : 0 ≤ 2*C)) (abs_nonneg (b i-b j))
    have hn1 : 0 ≤ C*((2:ℝ)^(J i))^2*|a i-a j|^(2/3:ℝ) := by positivity
    have hn2 : 0 ≤ C*((2:ℝ)^(J i))^2*|b i-b j| := by positivity
    nlinarith [hi i j]
  have hopB (i) (x : EuclideanSpace ℝ (Fin (n+1)×ι)) : ‖matrixMap (B i) x‖^2 ≤ ‖x‖^2 := by
    dsimp [B]
    rw [matrixMap_mul]
    exact (hop i _).trans (coisometry_operator _ (evaluation_coisometry r hr hr1 n (t i)) x)
  have hh := classified_survival B (fun i => (a i,b i)) (fun i => ⟨(ha i).1,(ha i).2,(hb i).1,(hb i).2⟩) J
    (by positivity : 0 ≤ 10*C) hbase hd hopB
  apply hh.trans (measure_mono ?_)
  intro x hx i
  apply (hx i).trans
  have hm := mul_le_mul_of_nonneg_left (sizeClass_sqrt (hk i))
    (by positivity : 0 ≤ 400*(64*(10*C)+2))
  nlinarith

end GaussianAR

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.Survival
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Gaussian path survival with slab and state constraints. -/

section

open MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace ENNReal
namespace GaussianEvents
variable {E F I : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_closed (A : I → E →L[ℝ] F) (R : I → ℝ) : IsClosed (constraints A R) := by
  simp only [constraints,Set.ofPred_forall]
  exact isClosed_iInter fun i => isClosed_le (A i).continuous.norm continuous_const

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_convex (A : I → E →L[ℝ] F) (R : I → ℝ) : Convex ℝ (constraints A R) := by
  have he : constraints A R = ⋂ i,(A i) ⁻¹' Metric.closedBall 0 (R i) := by
    ext x; simp [constraints,Metric.mem_closedBall,dist_zero_right]
  rw [he]
  exact convex_iInter fun i => (convex_closedBall (0:F) (R i)).linear_preimage (A i).toLinearMap

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
lemma constraints_symmetric (A : I → E →L[ℝ] F) (R : I → ℝ) :
    ∀ x ∈ constraints A R,-x ∈ constraints A R := by
  intro x hx i
  simpa only [map_neg,norm_neg] using hx i

lemma finite_half {J : Type*} [Fintype J] (K : J → Set E)
    (hc : ∀ i,IsClosed (K i)) (hv : ∀ i,Convex ℝ (K i))
    (hs : ∀ i,∀ x∈K i,-x∈K i)
    (hp : ∀ i,(1/2:ℝ≥0∞) ≤ stdGaussian E (K i)) :
    (1/2:ℝ)^(Fintype.card J) ≤ (stdGaussian E).real (⋂ i,K i) := by
  classical
  have h := EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
    (ContinuousLinearMap.id ℝ E) Finset.univ K (fun i _ => hc i) (fun i _ => hv i) (fun i _ => hs i)
  have he : (stdGaussian E).map (ContinuousLinearMap.id ℝ E) = stdGaussian E := Measure.map_id
  rw [he] at h
  have hh : (∏ i,(stdGaussian E).real (K i)) ≤ (stdGaussian E).real (⋂ i,K i) := by
    simpa using h
  apply le_trans _ hh
  change (1/2:ℝ)^(Finset.univ : Finset J).card ≤ _
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => by norm_num) (fun i _ => by
    have hh := ENNReal.toReal_mono (measure_ne_top _ _) (hp i)
    norm_num [Measure.real] at hh ⊢
    exact hh)

end GaussianEvents

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace BigOperators
namespace GaussianAR
open GaussianTail
variable {ι κ I : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype I]

lemma epoch_survival (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (n : ℕ) (F : I → Matrix κ ι ℝ) (h k : I → ℝ)
    {H C θ : ℝ} (hH : 0≤H) (hC : 0≤C) (hθ : 0≤θ)
    (hh : ∀ i,h i ∈ Set.Icc (0:ℝ) H) (hk : ∀ i,1/4≤k i)
    (hs : ∀ i,squareMass (F i) ≤ C*k i)
    (hi : ∀ i j,⌊h i⌋₊=⌊h j⌋₊ → squareMass (F i-F j) ≤
      C*(1+k i+k j)*|h i-h j|^(2/3:ℝ))
    (ht : ∀ i,(F i*diagonal (fun j => 1-r j)*(F i).transpose).trace ≤ C*k i*θ)
    (hop : ∀ i x,‖matrixMap (F i) x‖^2 ≤ ‖x‖^2) :
    Real.exp (-(H+1)*(θ*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
      {x | ∀ i (t : Fin (n+1)), ‖matrixMap (F i*evaluation r n t) x‖ ≤
        800*(640*C+2)*Real.sqrt (k i)} := by
  classical
  let J := Fin (⌊H⌋₊+1) × Fin (⌊θ*n⌋₊+1)
  let label (p : I × Fin (n+1)) : J :=
    (⟨⌊h p.1⌋₊,Nat.lt_succ_of_le (Nat.floor_mono (hh p.1).2)⟩,
      ⟨⌊θ*(p.2.val:ℝ)⌋₊,Nat.lt_succ_of_le (Nat.floor_mono
        (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.le_of_lt_succ p.2.isLt) hθ))⟩)
  let B (j : J) := {p : I × Fin (n+1) // label p=j}
  let A (j : J) (p : B j) := matrixMap (F p.val.1*evaluation r n p.val.2)
  let R (j : J) (p : B j) := 800*(640*C+2)*Real.sqrt (k p.val.1)
  let K (j : J) := GaussianEvents.constraints (A j) (R j)
  have hp (j : J) : (1/2:ℝ≥0∞) ≤ stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι)) (K j) := by
    let a (p : B j) := h p.val.1-(j.1.val:ℝ)
    let b (p : B j) := θ*(p.val.2.val:ℝ)-(j.2.val:ℝ)
    have hla (p : B j) : ⌊h p.val.1⌋₊=j.1.val := congrArg (fun z : J => z.1.val) p.property
    have hlb (p : B j) : ⌊θ*(p.val.2.val:ℝ)⌋₊=j.2.val := congrArg (fun z : J => z.2.val) p.property
    have ha (p : B j) : a p ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [a]; rw [← hla p]
      exact ⟨sub_nonneg.mpr (Nat.floor_le (hh p.val.1).1),by linarith [Nat.lt_floor_add_one (h p.val.1)]⟩
    have hb (p : B j) : b p ∈ Set.Icc (0:ℝ) 1 := by
      dsimp [b]; rw [← hlb p]
      exact ⟨sub_nonneg.mpr (Nat.floor_le (by positivity)),by linarith [Nat.lt_floor_add_one (θ*(p.val.2.val:ℝ))]⟩
    have hinc (p q : B j) : squareMass (F p.val.1-F q.val.1) ≤
        C*(1+k p.val.1+k q.val.1)*|a p-a q|^(2/3:ℝ) := by
      simpa only [a,sub_sub_sub_cancel_right] using hi p.val.1 q.val.1 ((hla p).trans (hla q).symm)
    have htime (p q : B j) : θ*|((p.val.2).val:ℝ)-(q.val.2).val| ≤ |b p-b q| := by
      dsimp [b]
      rw [sub_sub_sub_cancel_right,← mul_sub,abs_mul,abs_of_nonneg hθ]
    exact block_survival r hr hr1 n (fun p : B j => F p.val.1) (fun p => p.val.2)
      a b (fun p => k p.val.1) ha hb (fun p => hk p.val.1) hC
      (fun p => hs p.val.1) hinc (fun p => ht p.val.1) htime (fun p => hop p.val.1)
  have hprob := GaussianEvents.finite_half K
    (fun j => GaussianEvents.constraints_closed (A j) (R j))
    (fun j => GaussianEvents.constraints_convex (A j) (R j))
    (fun j => GaussianEvents.constraints_symmetric (A j) (R j)) hp
  have he : (⋂ j,K j)={x | ∀ i (t : Fin (n+1)), ‖matrixMap (F i*evaluation r n t) x‖ ≤
        800*(640*C+2)*Real.sqrt (k i)} := by
    ext x
    simp only [Set.mem_iInter,Set.mem_ofPred_eq,K,GaussianEvents.constraints]
    constructor
    · intro hx i t; exact hx (label (i,t)) ⟨(i,t),rfl⟩
    · intro hx j p; exact hx p.val.1 p.val.2
  rw [he] at hprob
  apply le_trans _ hprob
  have hcard : (Fintype.card J:ℝ) ≤ (H+1)*(θ*n+1) := by
    simp only [J,Fintype.card_prod,Fintype.card_fin,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
    exact mul_le_mul (by linarith [Nat.floor_le hH]) (by linarith [Nat.floor_le (show 0≤θ*n by positivity)])
      (by positivity) (by linarith)
  calc
    _ ≤ Real.exp (-(Fintype.card J:ℝ)) := Real.exp_le_exp.mpr (by nlinarith)
    _ = (Real.exp (-1))^(Fintype.card J) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ _ := pow_le_pow_left₀ (by positivity) (by
      have hg := Real.add_one_le_exp (1:ℝ)
      rw [Real.exp_neg]
      exact (inv_le_comm₀ (Real.exp_pos _) (by norm_num)).mpr (by norm_num; linarith)) _

end GaussianAR

end

section

open Matrix MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient Gain Energy GaussianTail GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

lemma epochFactor_ge_one : 1≤epochFactor := by
  unfold epochFactor
  linarith [gainConstant_pos]
lemma momentConstant_ge : 16≤ momentConstant := by
  unfold momentConstant
  linarith [incrementConstant_pos]
lemma survivalRadius_pos : 0<survivalRadius := by
  unfold survivalRadius
  linarith [momentConstant_ge]

omit [DecidableEq ι] [DecidableEq κ] in
lemma squareMass_sub_comm (A B : Matrix ι κ ℝ) : squareMass (A-B)=squareMass (B-A) := by
  unfold squareMass
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply]
  ring

lemma filtered_epoch_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j) {θ : ℝ} (hθ : 0<θ)
    (r : κ → ℝ) (hr : ∀ j,0≤r j) (hr1 : ∀ j,r j≤1) (hrq : ∀ j,1-r j≤q j) (n : ℕ) :
    let qθ := fun j => q j/θ
    let F := fun t => lift (run R (ps t)) (cfc cutoff (state qθ (run R (ps t))))
    let k := fun t => (cfc sizeWeight (state qθ (run R (ps t)))).trace
    Real.exp (-(epochFactor*cost (state qθ R) (L.map (fun p => p.move qθ))+1)*(θ*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
      {x | ∀ t (u : Fin (n+1)), ‖matrixMap (F t*evaluation r n u) x‖ ≤ survivalRadius*Real.sqrt (k t)} := by
  classical
  dsimp only
  let qθ := fun j => q j/θ
  let F := fun t => lift (run R (ps t)) (cfc cutoff (state qθ (run R (ps t))))
  let k := fun t => (cfc sizeWeight (state qθ (run R (ps t)))).trace
  let e := fun t => cost (state qθ R) ((ps t).map (fun p => p.move qθ))
  let H := epochFactor*cost (state qθ R) (L.map (fun p => p.move qθ))
  let h := fun t => epochFactor*e t
  have hqθ : ∀ j,0<qθ j := fun j => div_pos (hq j) hθ
  have hR' (t : T) : run R (ps t)*(run R (ps t)).transpose=1 :=
    run_coisometry hR (good_prefix hp (hps t)) (fresh_prefix hf (hps t)) (nodup_prefix hd (hps t))
  have hX (t : T) : (state qθ (run R (ps t))).PosDef := state_posDef (hR' t) hqθ
  have hk0 (t : T) : 0≤k t := by
    change 0 ≤ (cfc sizeWeight (state qθ (run R (ps t)))).trace
    rw [trace_cfc (hX t).1]
    exact Finset.sum_nonneg fun i _ => Scale.size_nonneg ((hX t).eigenvalues_pos i).le
  have he0 (t : T) : 0≤e t := cost_nonneg (state_posDef hR hqθ).posSemidef
    (moves_good (good_prefix hp (hps t)) (fun j => (hqθ j).le))
  have hfac : 0<epochFactor := lt_of_lt_of_le (by norm_num) epochFactor_ge_one
  have hH : 0≤H := mul_nonneg hfac.le
    (cost_nonneg (state_posDef hR hqθ).posSemidef (moves_good hp (fun j => (hqθ j).le)))
  have hh (t : T) : h t ∈ Set.Icc (0:ℝ) H := by
    refine ⟨mul_nonneg hfac.le (he0 t),mul_le_mul_of_nonneg_left ?_ hfac.le⟩
    exact cost_prefix (state_posDef hR hqθ).posSemidef (moves_good hp (fun j => (hqθ j).le))
      ((hps t).map _)
  have he_mono {s t : T} (hst : ps s <+: ps t) : e s≤e t :=
    cost_prefix (state_posDef hR hqθ).posSemidef
      (moves_good (good_prefix hp (hps t)) (fun j => (hqθ j).le)) (hst.map _)
  have hlocal {s t : T} (hst : ps s <+: ps t) (hab : ⌊h s⌋₊=⌊h t⌋₊) :
      squareMass (F t-F s) ≤ momentConstant*(1+k s+k t)*|h s-h t|^(2/3:ℝ) := by
    have hen : 0≤e t-e s := sub_nonneg.mpr (he_mono hst)
    have hex : |h s-h t|=epochFactor*(e t-e s) := by
      rw [abs_sub_comm,abs_of_nonneg (sub_nonneg.mpr
        (mul_le_mul_of_nonneg_left (he_mono hst) hfac.le))]
      ring
    have hsmall : e t-e s ≤ 1/(16*gainConstant) := by
      have ht := Nat.lt_floor_add_one (h t)
      rw [← hab] at ht
      have hss := Nat.floor_le (hh s).1
      have hdiff : epochFactor*(e t-e s) ≤ 1 := by dsimp [h] at ht hss; linarith
      apply (le_div_iff₀ (mul_pos (by norm_num) gainConstant_pos)).mpr
      have hscale : 16*gainConstant≤epochFactor := by unfold epochFactor; linarith
      nlinarith [mul_le_mul_of_nonneg_right hscale hen]
    have hi := local_prefix_increment hR hp hf hd hst (hps t) hqθ hsmall
    have hip : (e t-e s)^(1/exponent) ≤ |h s-h t|^(2/3:ℝ) := by
      rw [show 1/exponent=(2/3:ℝ) by norm_num [exponent]]
      apply Real.rpow_le_rpow hen
      · rw [hex]; nlinarith [epochFactor_ge_one]
      · norm_num
    have hinc : incrementConstant*(1+k t) ≤ momentConstant*(1+k s+k t) := by
      have hc : incrementConstant≤ momentConstant := by unfold momentConstant; linarith
      exact mul_le_mul hc (by linarith [hk0 s]) (by linarith [hk0 t]) (by linarith [momentConstant_ge])
    exact (squareMass_le_weighted (F t-F s) (fun j => (hqθ j).le)).trans
      (hi.trans (mul_le_mul hinc hip (Real.rpow_nonneg hen _) (mul_nonneg (by linarith [momentConstant_ge]) (by linarith [hk0 s,hk0 t]))))
  let I := {t : T // F t≠0}
  have hbound := epoch_survival r hr hr1 n (fun t : I => F t.val) (fun t => h t.val)
    (fun t => k t.val) hH (show 0≤ momentConstant by linarith [momentConstant_ge]) hθ.le
    (fun t => hh t.val) (fun t => lift_cutoff_size (hX t.val).posSemidef t.property)
    (fun t => (lift_cutoff_mass (hR' t.val) (hX t.val).posSemidef).trans
      (mul_le_mul_of_nonneg_right (by linarith [momentConstant_ge]) (hk0 t.val)))
    (by
      intro s t hab
      rcases List.prefix_or_prefix_of_prefix (hps s.val) (hps t.val) with hst|hts
      · rw [squareMass_sub_comm]
        exact hlocal hst hab
      · have hu := hlocal hts hab.symm
        simpa only [abs_sub_comm,add_comm,add_left_comm,add_assoc] using hu)
    (by
      intro t
      change weightedSq (F t.val) (diagonal (fun j => 1-r j))≤_
      exact (weightedSq_diagonal_mono _ hrq).trans ((lift_cutoff_time (hR' t.val) hq hθ).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (by linarith [momentConstant_ge]) (hk0 t.val)) hθ.le)))
    (fun t => lift_cutoff_contract (hR' t.val) (hX t.val).1)
  apply hbound.trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro x hx t u
  change ‖matrixMap (F t*evaluation r n u) x‖ ≤ survivalRadius*Real.sqrt (k t)
  by_cases ht : F t=0
  · simp only [ht,Matrix.zero_mul,matrixMap,map_zero,_root_.zero_apply,norm_zero]
    exact mul_nonneg survivalRadius_pos.le (Real.sqrt_nonneg _)
  · exact hx ⟨t,ht⟩ u

end EuclideanSteinitz.Filter

end

section

open Matrix GaussianTail
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [DecidableEq ι] in
lemma state_scale (q : κ → ℝ) (R : Matrix ι κ ℝ) (θ : ℝ) :
    state (fun j => q j/θ) R = θ⁻¹ • state q R := by
  unfold state
  have he : diagonal (fun j => q j/θ) = θ⁻¹ • diagonal q := by
    rw [← Matrix.diagonal_smul]
    congr 1
    ext j
    simp [div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mul_smul,Matrix.smul_mul]

lemma sum_scale_size {A : Matrix ι ι ℝ} (hA : A.PosDef) (S : Finset ℤ) :
    (∑ k ∈ S,(cfc sizeWeight (((2:ℝ)^k)⁻¹ • A)).trace) ≤ 14*Fintype.card ι := by
  simp only [cfc_scaled hA.1,trace_cfc hA.1]
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ i : ι,(14:ℝ) := Finset.sum_le_sum fun i _ => by
      simpa only [div_eq_mul_inv,mul_comm] using Scale.sum_size_dyadic S (hA.eigenvalues_pos i)
    _ = _ := by simp [mul_comm]

lemma form_mono {A B : Matrix ι ι ℝ} (hAB : A≤B) (x : EuclideanSpace ℝ ι) :
    ⟪x,toEuclideanCLM (𝕜 := ℝ) A x⟫ ≤ ⟪x,toEuclideanCLM (𝕜 := ℝ) B x⟫ := by
  have h := (Matrix.le_iff.mp hAB).dotProduct_mulVec_nonneg (WithLp.ofLp x)
  simpa only [star_trivial,Matrix.sub_mulVec,dotProduct_sub,inner_toEuclideanCLM,sub_nonneg] using h

lemma cutoff_cover {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤hA.eigenvalues i/(2:ℝ)^k ∧ hA.eigenvalues i/(2:ℝ)^k≤2) :
    (1 : Matrix ι ι ℝ) ≤ ∑ k∈S,cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A) := by
  have he (k : ℤ) : cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A) =
      cfc (fun x => cutoff (x/(2:ℝ)^k)^2) A := by
    rw [cfc_scaled hA,cfc_mul_same hA]
    congr 1
    ext x
    simp [div_eq_mul_inv,mul_comm,pow_two]
  simp only [he]
  rw [← cfc_sum _ A S (fun _ _ => Gain.finite_spectrum_continuous _ _)]
  rw [← cfc_const_one ℝ A]
  apply (cfc_le_iff _ _ A continuousOn_const (Gain.finite_spectrum_continuous _ _) hA.isSelfAdjoint).mpr
  intro x hx
  obtain ⟨i,rfl⟩ := hA.spectrum_real_eq_range_eigenvalues ▸ hx
  obtain ⟨k,hk,hk1,hk2⟩ := hS i
  simp only [Finset.sum_apply]
  change 1≤∑ k∈S,cutoff (hA.eigenvalues i/(2:ℝ)^k)^2
  have hh := Finset.single_le_sum (fun j (_ : j∈S) => sq_nonneg (cutoff (hA.eigenvalues i/(2:ℝ)^j))) hk
  have hone : cutoff (hA.eigenvalues i/(2:ℝ)^k)=1 := by
    simp [cutoff,show (2:ℝ)⁻¹ < hA.eigenvalues i/(2:ℝ)^k by norm_num; linarith,not_lt.mpr hk1,hk2]
  rwa [hone,one_pow] at hh

omit [DecidableEq κ] in
lemma lift_gram {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {A : Matrix ι ι ℝ} (hA : A.transpose=A) :
    (lift R A).transpose*lift R A = R.transpose*(A*A)*R := by
  simp only [lift,Matrix.transpose_mul,Matrix.transpose_transpose,hA]
  calc
    _ = R.transpose*A*(R*R.transpose)*A*R := by simp only [Matrix.mul_assoc]
    _ = _ := by rw [hR,Matrix.mul_one]; simp only [Matrix.mul_assoc]

lemma norm_sq_reconstruct {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤hA.eigenvalues i/(2:ℝ)^k ∧ hA.eigenvalues i/(2:ℝ)^k≤2)
    (x : EuclideanSpace ℝ κ) :
    ‖matrixMap R x‖^2 ≤ ∑ k∈S,‖matrixMap (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A))) x‖^2 := by
  have hp := (Matrix.le_iff.mp (cutoff_cover hA S hS)).mul_mul_conjTranspose_same R.transpose
  simp only [conjTranspose_eq_transpose_of_trivial,transpose_transpose,Matrix.mul_sub,Matrix.sub_mul,
    Matrix.mul_one,Matrix.mul_sum,Matrix.sum_mul] at hp
  have hh := form_mono (Matrix.le_iff.mpr hp) x
  rw [gram_form] at hh
  have he (k : ℤ) : R.transpose*(cfc cutoff (((2:ℝ)^k)⁻¹ • A)*cfc cutoff (((2:ℝ)^k)⁻¹ • A))*R =
      (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A))).transpose*lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • A)) :=
    (lift_gram hR (cfc_transpose (hA.smul (IsSelfAdjoint.all _)) cutoff)).symm
  simp only [he,map_sum,_root_.sum_apply,inner_sum,gram_form] at hh
  exact hh

lemma exists_finite_scales {T : Type*} [Fintype T] (A : T → Matrix ι ι ℝ)
    (hA : ∀ t,(A t).PosDef) :
    ∃ S : Finset ℤ, (∀ t i,∃ k∈S,1≤(hA t).1.eigenvalues i/(2:ℝ)^k ∧
      (hA t).1.eigenvalues i/(2:ℝ)^k≤2) ∧
      (∀ k∈S,∃ t i,(2:ℝ)^k≤(hA t).1.eigenvalues i) := by
  classical
  choose f hf using fun t i => Scale.dyadic_normalize ((hA t).eigenvalues_pos i)
  refine ⟨Finset.univ.image (fun p : T×ι => f p.1 p.2),?_,?_⟩
  · intro t i
    exact ⟨f t i,Finset.mem_image.mpr ⟨(t,i),Finset.mem_univ _,rfl⟩,hf t i⟩
  · intro k hk
    obtain ⟨⟨t,i⟩,_,rfl⟩ := Finset.mem_image.mp hk
    exact ⟨t,i,(le_div_iff₀ (zpow_pos (by norm_num) _)).mp (hf t i).1 |>.trans' (by simp)⟩

end EuclideanSteinitz.Filter

end

section

open Matrix MeasureTheory ProbabilityTheory Set
open scoped RealInnerProductSpace
namespace GaussianEvents
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma finite_exp {J : Type*} [Fintype J] (K : J → Set E) (c : J → ℝ)
    (hc : ∀ i,IsClosed (K i)) (hv : ∀ i,Convex ℝ (K i))
    (hs : ∀ i,∀ x∈K i,-x∈K i)
    (hp : ∀ i,Real.exp (-c i) ≤ (stdGaussian E).real (K i)) :
    Real.exp (-(∑ i,c i)) ≤ (stdGaussian E).real (⋂ i,K i) := by
  classical
  have hh := EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
    (ContinuousLinearMap.id ℝ E) Finset.univ K (fun i _ => hc i) (fun i _ => hv i) (fun i _ => hs i)
  have he : (stdGaussian E).map (ContinuousLinearMap.id ℝ E) = stdGaussian E := Measure.map_id
  rw [he] at hh
  have hp' : (∏ i,Real.exp (-c i)) ≤ ∏ i,(stdGaussian E).real (K i) :=
    Finset.prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) (fun i _ => hp i)
  simpa only [← Real.exp_sum,Finset.sum_neg_distrib,Finset.mem_univ,Set.iInter_true] using hp'.trans hh

end GaussianEvents

namespace GaussianAR
open GaussianTail EuclideanSteinitz.Coefficient EuclideanSteinitz.Filter
variable {ι κ J : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]  [Fintype J]
lemma slabRadius_pos : 0<slabRadius := by norm_num [slabRadius]

lemma weighted_diagonal_eq (A : Matrix κ ι ℝ) (q : ι → ℝ) :
    weightedSq A (diagonal q) = ∑ j,∑ i,q i*(A j i)^2 := by
  change (∑ j,∑ i,(A*diagonal q) j i*A j i)=_
  simp only [Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma one_slab_survival (A : Matrix κ ι ℝ) (hA : squareMass A ≤ 1)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (q : ι → ℝ) (hq : ∀ i,0≤q i) (hrq : ∀ i,1-r i≤q i) (n : ℕ) :
    Real.exp (-(weightedSq A (diagonal q)*n+1)) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ t : Fin (n+1),‖matrixMap (A*evaluation r n t) x‖ ≤ slabRadius} := by
  have ht : 0≤weightedSq A (diagonal q) := weightedSq_nonneg A (PosSemidef.diagonal hq)
  have hh := epoch_survival r hr hr1 n (fun _ : Unit => A) (fun _ => 0) (fun _ => 1)
    (H := 0) (C := 1) (θ := weightedSq A (diagonal q)) (by norm_num) (by norm_num) ht
    (fun _ => by simp) (fun _ => by norm_num) (fun _ => by simpa using hA)
    (by intros; simp [squareMass])
    (fun _ => by
      change weightedSq A (diagonal (fun i => 1-r i)) ≤ 1*1*weightedSq A (diagonal q)
      simpa only [one_mul] using weightedSq_diagonal_mono A hrq)
    (fun _ x => (norm_sq_le_squareMass A x).trans (by nlinarith [sq_nonneg ‖x‖]))
  simpa only [zero_add,neg_mul,one_mul,Real.sqrt_one,mul_one,forall_const,slabRadius] using hh

lemma slabs_survival (A : J → Matrix κ ι ℝ) (hA : ∀ j,squareMass (A j) ≤ 1)
    (r : ι → ℝ) (hr : ∀ i,0≤r i) (hr1 : ∀ i,r i≤1)
    (q : ι → ℝ) (hq : ∀ i,0≤q i) (hrq : ∀ i,1-r i≤q i) (n : ℕ) :
    Real.exp (-(Fintype.card J:ℝ)-(∑ j,weightedSq (A j) (diagonal q))*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×ι))).real
        {x | ∀ j (t : Fin (n+1)),‖matrixMap (A j*evaluation r n t) x‖ ≤ slabRadius} := by
  let K := fun j => GaussianEvents.constraints (fun t : Fin (n+1) => matrixMap (A j*evaluation r n t)) (fun _ => slabRadius)
  have hh := GaussianEvents.finite_exp K (fun j => weightedSq (A j) (diagonal q)*n+1)
    (fun j => GaussianEvents.constraints_closed _ _) (fun j => GaussianEvents.constraints_convex _ _)
    (fun j => GaussianEvents.constraints_symmetric _ _) (fun j => one_slab_survival (A j) (hA j) r hr hr1 q hq hrq n)
  have he : (⋂ j,K j)={x | ∀ j (t : Fin (n+1)),‖matrixMap (A j*evaluation r n t) x‖ ≤ slabRadius} := by
    ext x; simp only [K,GaussianEvents.constraints,Set.mem_iInter,Set.mem_ofPred_eq]
  rw [he] at hh
  convert hh using 1
  congr 1
  simp only [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  ring

end GaussianAR

end

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace
namespace EuclideanSteinitz.Filter
open MatrixEnergy Spectral Coefficient ScaleMatrix ScaleEnergy Energy GaussianAR
variable {ι κ T : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] [Fintype T]

lemma stateRadius_pos : 0 < stateRadius := mul_pos (by norm_num) survivalRadius_pos

omit [DecidableEq ι] in
lemma matrixMap_mul_apply {ν : Type*} [Fintype ν] [DecidableEq ν]
    (A : Matrix ι κ ℝ) (B : Matrix κ ν ℝ) (x : EuclideanSpace ℝ ν) :
    matrixMap (A*B) x = matrixMap A (matrixMap B x) := by
  apply WithLp.ofLp_injective
  exact Matrix.mulVec_mulVec x A B |>.symm

lemma reconstruction_bound {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {q : κ → ℝ} (hq : ∀ j,0<q j) (S : Finset ℤ)
    (hS : ∀ i,∃ k∈S,1≤(state_posDef hR hq).1.eigenvalues i/(2:ℝ)^k ∧
      (state_posDef hR hq).1.eigenvalues i/(2:ℝ)^k≤2)
    (x : EuclideanSpace ℝ κ)
    (hx : ∀ k∈S,‖matrixMap (lift R (cfc cutoff (state (fun j => q j/(2:ℝ)^k) R))) x‖ ≤
      survivalRadius*Real.sqrt ((cfc sizeWeight (state (fun j => q j/(2:ℝ)^k) R)).trace)) :
    ‖matrixMap R x‖ ≤ stateRadius*Real.sqrt (Fintype.card ι) := by
  have hA := state_posDef hR hq
  have hrec := norm_sq_reconstruct hR hA.1 S hS x
  have hk (k : ℤ) : 0≤(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace := by
    rw [cfc_scaled hA.1,trace_cfc hA.1]
    exact Finset.sum_nonneg fun i _ => Scale.size_nonneg (mul_nonneg (inv_nonneg.mpr (zpow_pos (by norm_num) _).le) (hA.eigenvalues_pos i).le)
  have hb : (∑ k∈S,‖matrixMap (lift R (cfc cutoff (((2:ℝ)^k)⁻¹ • state q R))) x‖^2) ≤
      survivalRadius^2*(14*Fintype.card ι) := by
    calc
      _ ≤ ∑ k∈S,survivalRadius^2*(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace := by
        apply Finset.sum_le_sum
        intro k hkS
        have hh := pow_le_pow_left₀ (norm_nonneg _) (hx k hkS) 2
        simpa only [state_scale,mul_pow,Real.sq_sqrt (hk k)] using hh
      _ = survivalRadius^2*(∑ k∈S,(cfc sizeWeight (((2:ℝ)^k)⁻¹ • state q R)).trace) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (sum_scale_size hA S) (sq_nonneg _)
  have hs := Real.sq_sqrt (show (0:ℝ)≤Fintype.card ι by positivity)
  have hp : 0 ≤ stateRadius*Real.sqrt (Fintype.card ι) := mul_nonneg stateRadius_pos.le (Real.sqrt_nonneg _)
  have ht : ‖matrixMap R x‖^2 ≤ (stateRadius*Real.sqrt (Fintype.card ι))^2 := by
    apply hrec.trans (hb.trans _)
    rw [mul_pow,hs,stateRadius]
    nlinarith [mul_nonneg (sq_nonneg survivalRadius) (show (0:ℝ)≤Fintype.card ι by positivity)]
  exact (sq_le_sq₀ (norm_nonneg _) hp).mp ht

lemma state_survival {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    {q : κ → ℝ} (hq : ∀ j,0<q j)
    (r : κ → ℝ) (hr : ∀ j,0≤r j) (hr1 : ∀ j,r j≤1) (hrq : ∀ j,1-r j≤q j) :
    ∃ a : ℝ,∀ n : ℕ,
      Real.exp (-a-stateRate*(∑ j,q j)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
        {x | ∀ t (u : Fin (n+1)),‖matrixMap (run R (ps t)*evaluation r n u) x‖ ≤ stateRadius*Real.sqrt (Fintype.card ι)} := by
  classical
  let Rt := fun t => run R (ps t)
  have hRt (t : T) : Rt t*(Rt t).transpose=1 :=
    run_coisometry hR (good_prefix hp (hps t)) (fresh_prefix hf (hps t)) (nodup_prefix hd (hps t))
  let A := fun t => state q (Rt t)
  have hA (t : T) : (A t).PosDef := state_posDef (hRt t) hq
  obtain ⟨S,hS,hS'⟩ := exists_finite_scales A hA
  let e := fun k : ℤ => cost (state (fun j => q j/(2:ℝ)^k) R) (L.map (fun p => p.move (fun j => q j/(2:ℝ)^k)))
  let c := fun k : ℤ => epochFactor*e k+1
  have htq : 0≤∑ j,q j := Finset.sum_nonneg fun j _ => (hq j).le
  have hθ (k : ℤ) (hk : k∈S) : (2:ℝ)^k ≤ ∑ j,q j := by
    obtain ⟨t,i,hi⟩ := hS' k hk
    apply hi.trans
    have htrace : (hA t).1.eigenvalues i ≤ (A t).trace := by
      rw [trace_spectral (hA t).1]
      exact Finset.single_le_sum (fun j _ => (hA t).eigenvalues_pos j |>.le) (Finset.mem_univ i)
    exact htrace.trans (state_trace_le (hRt t) (fun j => (hq j).le))
  have hrate : (∑ k : S,c k.val*(2:ℝ)^k.val) ≤ stateRate*(∑ j,q j) := by
    have he := sum_epoch_cost hR hp hd (fun j => (hq j).le) S
    have ht := sum_dyadic_le htq hθ
    simp only [← state_scale] at he
    have hsum : (∑ k : S,c k.val*(2:ℝ)^k.val) =
        epochFactor*(∑ k∈S,(2:ℝ)^k*e k)+(∑ k∈S,(2:ℝ)^k) := by
      rw [Finset.sum_coe_sort S (fun k => c k*(2:ℝ)^k),Finset.mul_sum,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      dsimp [c]
      ring
    rw [hsum]
    unfold stateRate
    nlinarith [mul_le_mul_of_nonneg_left he (show 0≤epochFactor by linarith [epochFactor_ge_one])]
  refine ⟨∑ k : S,c k.val,fun n => ?_⟩
  let F := fun k : S => fun t => lift (Rt t) (cfc cutoff (state (fun j => q j/(2:ℝ)^k.val) (Rt t)))
  let w := fun k : S => fun t => survivalRadius*Real.sqrt ((cfc sizeWeight (state (fun j => q j/(2:ℝ)^k.val) (Rt t))).trace)
  let K := fun k : S => GaussianEvents.constraints
    (fun p : T×Fin (n+1) => matrixMap (F k p.1*evaluation r n p.2)) (fun p => w k p.1)
  have hprob := GaussianEvents.finite_exp K (fun k : S => c k.val*((2:ℝ)^k.val*n+1))
    (fun k => GaussianEvents.constraints_closed _ _) (fun k => GaussianEvents.constraints_convex _ _)
    (fun k => GaussianEvents.constraints_symmetric _ _) (fun k => by
      have hh := filtered_epoch_survival hR hp hf hd ps hps hq (θ := (2:ℝ)^k.val) (zpow_pos (by norm_num) k.val) r hr hr1 hrq n
      dsimp only at hh
      convert hh using 1
      · dsimp [c,e]; congr 1; ring
      · congr 1
        ext x
        simp only [K,GaussianEvents.constraints,Set.mem_ofPred_eq,Prod.forall]
        rfl)
  have hlow : Real.exp (-(∑ k : S,c k.val)-stateRate*(∑ j,q j)*n) ≤
      Real.exp (-(∑ k : S,c k.val*((2:ℝ)^k.val*n+1))) := by
    apply Real.exp_le_exp.mpr
    have heq : (∑ k : S,c k.val*((2:ℝ)^k.val*n+1)) =
        (∑ k : S,c k.val)+(∑ k : S,c k.val*(2:ℝ)^k.val)*n := by
      simp only [mul_add,mul_one,Finset.sum_add_distrib,← mul_assoc,← Finset.sum_mul]
      ring
    rw [heq]
    nlinarith [mul_le_mul_of_nonneg_right hrate (Nat.cast_nonneg n : (0:ℝ)≤n)]
  apply hlow.trans (hprob.trans _)
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx t u
  rw [matrixMap_mul_apply]
  apply reconstruction_bound (hRt t) hq S (hS t) (matrixMap (evaluation r n u) x)
  intro k hk
  have hh := Set.mem_iInter.mp hx (⟨k,hk⟩ : S) (t,u)
  change ‖matrixMap (F ⟨k,hk⟩ t*evaluation r n u) x‖≤_ at hh
  rw [matrixMap_mul_apply] at hh
  exact hh

end EuclideanSteinitz.Filter

end

end OAI
end

section
-- module Solutions.OAIQW_EuclideanSteinitzBergstrom.FilteredBody
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

/-! Filtered-body energy and the predictor slab budget. -/

section

open Matrix GaussianTail MeasureTheory ProbabilityTheory Set
open scoped MatrixOrder Matrix.Norms.L2Operator RealInnerProductSpace Pointwise NNReal

namespace EuclideanSteinitz.Filter
open GaussianAR GaussianEvents Coefficient
variable {ι κ T J : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
  [Fintype T] [Fintype J] [Nonempty ι] [Nonempty κ]

omit [Nonempty κ] in
lemma slabs_rate (H : J → Matrix Unit κ ℝ) (hH : ∀ i,∑ j, (H j () i)^2 ≤ 1)
    {q : κ → ℝ} (hq : ∀ i,0≤q i) :
    (∑ j,weightedSq (H j) (diagonal q)) ≤ ∑ i,q i := by
  simp only [weighted_diagonal_eq,Fintype.sum_unique]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left (hH i) (hq i)

lemma applicationDomain_survival_oai {R : Matrix ι κ ℝ} (hR : R*R.transpose=1)
    {L : List (Step ι κ)} (hp : ∀ p∈L,p.Good) (hf : Fresh R L) (hd : (L.map Step.j).Nodup)
    (ps : T → List (Step ι κ)) (hps : ∀ t,ps t <+: L)
    (H : J → Matrix Unit κ ℝ) (hH : ∀ j,squareMass (H j)≤1) (hcol : ∀ i,∑ j,(H j () i)^2≤1)
    {q : κ → ℝ} (hq : ∀ i,0<q i) :
    ∃ a : ℝ,∀ n : ℕ,Real.exp (-a-bodyRate*(∑ i,q i)*n) ≤
      (stdGaussian (EuclideanSpace ℝ (Fin (n+1)×κ))).real
        {x | ∀ u : Fin (n+1),matrixMap (evaluation (fun i => (1+q i)⁻¹) n u) x ∈
          applicationDomain (fun t => run R (ps t)) H} := by
  let r : κ → ℝ := fun i => (1+q i)⁻¹
  have hr i : 0≤r i := inv_nonneg.mpr (by linarith [hq i])
  have hr1 i : r i≤1 := (inv_le_one₀ (by linarith [hq i])).mpr (by linarith [hq i])
  have hrq i : 1-r i≤q i := by
    dsimp [r]
    have hh : 1-q i≤1/(1+q i) := (le_div_iff₀ (by linarith [hq i])).mpr (by nlinarith [sq_nonneg (q i)])
    rw [one_div] at hh
    linarith
  obtain ⟨a,ha⟩ := state_survival hR hp hf hd ps hps hq r hr hr1 hrq
  obtain ⟨b,hb⟩ := state_survival (ι := κ) (R := 1) (by simp) (L := []) (by simp)
    (by simp [Fresh]) (by simp) (fun _ : Unit => []) (by simp) hq r hr hr1 hrq
  let w := ∑ j,weightedSq (H j) (diagonal q)
  have hw : w≤∑ i,q i := slabs_rate H hcol (fun i => (hq i).le)
  refine ⟨a+b+Fintype.card J,fun n => ?_⟩
  let A := constraints (fun p : T×Fin (n+1) => matrixMap (run R (ps p.1)*evaluation r n p.2))
    (fun _ => stateRadius*Real.sqrt (Fintype.card ι))
  let B := constraints (fun u : Fin (n+1) => matrixMap (evaluation r n u))
    (fun _ => stateRadius*Real.sqrt (Fintype.card κ))
  let C := constraints (fun p : J×Fin (n+1) => matrixMap (H p.1*evaluation r n p.2)) (fun _ => slabRadius)
  have hpa : Real.exp (-a-stateRate*(∑ i,q i)*n)≤(stdGaussian _).real A := by
    simpa only [A,constraints,Prod.forall] using ha n
  have hpb : Real.exp (-b-stateRate*(∑ i,q i)*n)≤(stdGaussian _).real B := by
    simpa only [B,constraints,run,Matrix.one_mul,forall_const] using hb n
  have hpc : Real.exp (-(Fintype.card J:ℝ)-w*n)≤(stdGaussian _).real C := by
    simpa only [C,constraints,Prod.forall,w] using slabs_survival H hH r hr hr1 q (fun i => (hq i).le) hrq n
  have hab := GaussianCorrelation.stdGaussian_closed_convex_correlation
    (constraints_closed _ _) (constraints_closed _ _) (constraints_convex _ _) (constraints_convex _ _)
    (constraints_symmetric _ _) (constraints_symmetric _ _) (K := A) (L := B)
  have habc := GaussianCorrelation.stdGaussian_closed_convex_correlation
    ((constraints_closed _ _).inter (constraints_closed _ _)) (constraints_closed _ _)
    ((constraints_convex _ _).inter (constraints_convex _ _)) (constraints_convex _ _)
    (fun x hx => ⟨constraints_symmetric _ _ x hx.1,constraints_symmetric _ _ x hx.2⟩)
    (constraints_symmetric _ _) (K := A∩B) (L := C)
  have hlow : Real.exp (-(a+b+Fintype.card J)-bodyRate*(∑ i,q i)*n) ≤
      Real.exp (-a-stateRate*(∑ i,q i)*n)*Real.exp (-b-stateRate*(∑ i,q i)*n)*Real.exp (-(Fintype.card J:ℝ)-w*n) := by
    rw [← Real.exp_add,← Real.exp_add]
    apply Real.exp_le_exp.mpr
    unfold bodyRate
    nlinarith [mul_le_mul_of_nonneg_right hw (Nat.cast_nonneg n : (0:ℝ)≤n)]
  apply hlow.trans
  apply le_trans (mul_le_mul (mul_le_mul hpa hpb (Real.exp_pos _).le (measureReal_nonneg)) hpc (Real.exp_pos _).le (mul_nonneg measureReal_nonneg measureReal_nonneg))
  apply le_trans (mul_le_mul_of_nonneg_right hab measureReal_nonneg)
  apply habc.trans
  apply measureReal_mono _ (measure_ne_top _ _)
  intro x hx u
  have hι : 0<stateRadius*Real.sqrt (Fintype.card ι) := mul_pos stateRadius_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  have hκ : 0<stateRadius*Real.sqrt (Fintype.card κ) := mul_pos stateRadius_pos (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos))
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro t
    have hh := hx.1.1 (t,u)
    change ‖matrixMap (run R (ps t)*evaluation r n u) x‖≤_ at hh
    rw [matrixMap_mul_apply] at hh
    change ‖matrixMap (run R (ps t)) (matrixMap (evaluation r n u) x)‖< _
    linarith
  · have hh := hx.1.2 u
    change ‖matrixMap (evaluation r n u) x‖≤_ at hh
    simp only [Metric.mem_ball,dist_zero_right]
    linarith
  · intro j
    have hh := hx.2 (j,u)
    change ‖matrixMap (H j*evaluation r n u) x‖≤_ at hh
    rw [matrixMap_mul_apply] at hh
    change ‖matrixMap (H j) (matrixMap (evaluation r n u) x)‖< _
    linarith [slabRadius_pos]

end EuclideanSteinitz.Filter

end

end OAI
end

theorem solution.{u_1, u_2, u_3, u_4} : type_of% @OAI.EuclideanSteinitz.Filter.applicationDomain_survival_oai.{u_1, u_2, u_3, u_4} := @OAI.EuclideanSteinitz.Filter.applicationDomain_survival_oai.{u_1, u_2, u_3, u_4}
