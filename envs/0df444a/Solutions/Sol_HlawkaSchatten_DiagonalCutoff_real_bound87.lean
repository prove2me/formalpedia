-- Prove2me | solution 1 for HlawkaSchatten.DiagonalCutoff.real_bound87
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-05T01:38:30.165975+00:00
-- url     : https://prove2.me/submissions/013b1a73-ee8c-47d3-bd71-a19ffea7eddb

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa

The cutoff-87 proof extends the accepted cutoff-90 solution (submission
2601ab00, by BrunoDCDO, adapting Ezzeri Esa's construction) and the cutoff-88
result. For `p ≥ 88` it imports `real_bound88`. On `87 ≤ p ≤ 88` it reruns the
localization and box-convexity argument with `q₀ = 5351/15000`, uses the
improved witness `(3/(4p))^{1/p}`, and closes the scalar comparisons by exact
polynomial certificates.
-/
import Mathlib
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_exponent
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_TailEstimates
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_denominator_pos
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_HessianBounds
import Mathlib.Tactic
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_normalized_failure
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_pair_sum_le
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ComplexTransfer
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_OrbitAveraging
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_CyclicWitness
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_real_bound_of_fin_three
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
import Theorems.Thm_HlawkaSchatten_DiagonalConstruction_convex_entryBox
import Theorems.Thm_HlawkaSchatten_DiagonalCutoff_real_bound88

set_option autoImplicit false



namespace HlawkaSchatten.DiagonalConstruction

/-! ### Scalar estimates on the window `88 ≤ p ≤ 90`

The `p ≥ 90` argument used first-order bounds that are uniform in `p`. On the
compact window `[89, 90]` we keep the second-order Taylor terms instead, with
`x = p⁻¹ ∈ [1/90, 1/88]`, split at `p = 89`, and close each comparison by an exact polynomial
certificate in `x`. -/

lemma cutoff88_inverse_bounds {p : ℝ} (hp : 88 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1 / 88 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩

lemma cutoff88_inverse_lower {p q : ℝ} (hp' : p ≤ q) (hp : 88 ≤ p) : 1 / q ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hp'

lemma cutoff89_log_ninety : Real.log (90 : ℝ) < 4499810 / 1000000 := by
  have heq : Real.log (90 : ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    rw [show (90 : ℝ) = 2 * (3 ^ 2) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  rw [heq]
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

lemma cutoff88_log_eightynine : Real.log (89 : ℝ) < 448870 / 100000 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 89 / 90 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num)] at h
  linarith [cutoff89_log_ninety]

lemma cutoff88_log_upper {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    Real.log p < 4499810 / 1000000 :=
  (Real.log_le_log (by linarith) hp').trans_lt cutoff89_log_ninety

lemma cutoff88_log_upper_low {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 89) :
    Real.log p < 448870 / 100000 :=
  (Real.log_le_log (by linarith) hp').trans_lt cutoff88_log_eightynine

lemma cutoff88_log_scaled {p Z : ℝ} (hp : 88 ≤ p) (hZ : Real.log p < Z) (hZ1 : Z ≤ 4499810 / 1000000) :
    0 ≤ Real.log p * p⁻¹ ∧ Real.log p * p⁻¹ ≤ Z * p⁻¹ ∧
      Real.log p * p⁻¹ < 1 / 19 := by
  have hi := cutoff88_inverse_bounds hp
  have hl := hZ
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  refine ⟨mul_nonneg hl0 hi.1.le, mul_le_mul_of_nonneg_right hl.le hi.1.le, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hl.le hi.1.le, mul_le_mul_of_nonneg_right hZ1 hi.1.le]

lemma cutoff88_exp_cubic {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 / 2 + 2 * x ^ 3 / 9 := by
  have h := Real.exp_bound' hx hx1 (n := 3) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma cutoff88_exp_neg_cubic {z : ℝ} (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z + z ^ 2 / 2 - 2 * z ^ 3 / 9 ≤ Real.exp (-z) := by
  have h := Real.exp_bound (x := -z) (n := 3) (by simpa [abs_of_nonneg hz]) (by norm_num)
  have he := (abs_sub_le_iff.mp h).2
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hz] at he
  nlinarith

/-- Lower bound for the cyclic numerator, as a polynomial in `x = p⁻¹`. -/
noncomputable def cutoff88Nlo (Z x : ℝ) : ℝ :=
  3 * (1 + (6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4) * x) ^ 2 / 2) -
    (1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9) *
      (1 + Z * x - (Z * x) ^ 2 / 2 + 2 * (Z * x) ^ 3 / 9)

/-- Upper bound for the cyclic denominator, as a polynomial in `x = p⁻¹`. -/
noncomputable def cutoff88Dup (x : ℝ) : ℝ :=
  6 * ((6931471808 / 10 ^ 10 + x / 2) * x + ((6931471808 / 10 ^ 10 + x / 2) * x) ^ 2 / 2 +
    2 * ((6931471808 / 10 ^ 10 + x / 2) * x) ^ 3 / 9)

/-- Lower bound for the envelope deficit, as a polynomial in `x = p⁻¹`. -/
noncomputable def cutoff88Glo (x : ℝ) : ℝ :=
  (6931471803 / 10 ^ 10 - x ^ 2 / 1000) * x - (6931471808 / 10 ^ 10 * x) ^ 2 / 2

set_option maxHeartbeats 4000000 in
/-- Exact certificate for the envelope comparison on `x ∈ [1/90, 1/89]`. -/
lemma cutoff88_envelope_certificate_high {x : ℝ} (h1 : 1 / 90 ≤ x) (h2 : x ≤ 1 / 89) :
    (1 - 107041 / 300000 : ℝ) * cutoff88Dup x <
      cutoff88Nlo (4499810 / 1000000) x * (2 * cutoff88Glo x) := by
  unfold cutoff88Dup cutoff88Nlo cutoff88Glo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 90 + s := ⟨x - 1 / 90, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 8010 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8, pow_nonneg hs 9, pow_nonneg hs 10,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

set_option maxHeartbeats 4000000 in
/-- Exact certificate for the linear witness bound on `x ∈ [1/90, 1/89]`. -/
lemma cutoff88_linear_certificate_high {x : ℝ} (h1 : 1 / 90 ≤ x) (h2 : x ≤ 1 / 89) :
    (20 / 43 : ℝ) * cutoff88Dup x < x * cutoff88Nlo (4499810 / 1000000) x := by
  unfold cutoff88Dup cutoff88Nlo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 90 + s := ⟨x - 1 / 90, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 8010 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

set_option maxHeartbeats 4000000 in
/-- Exact certificate for the envelope comparison on `x ∈ [1/89, 1/88]`. -/
lemma cutoff88_envelope_certificate_low {x : ℝ} (h1 : 1 / 89 ≤ x) (h2 : x ≤ 1 / 88) :
    (1 - 107041 / 300000 : ℝ) * cutoff88Dup x <
      cutoff88Nlo (448870 / 100000) x * (2 * cutoff88Glo x) := by
  unfold cutoff88Dup cutoff88Nlo cutoff88Glo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 89 + s := ⟨x - 1 / 89, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 7832 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8, pow_nonneg hs 9, pow_nonneg hs 10,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

set_option maxHeartbeats 4000000 in
/-- Exact certificate for the linear witness bound on `x ∈ [1/89, 1/88]`. -/
lemma cutoff88_linear_certificate_low {x : ℝ} (h1 : 1 / 89 ≤ x) (h2 : x ≤ 1 / 88) :
    (20 / 43 : ℝ) * cutoff88Dup x < x * cutoff88Nlo (448870 / 100000) x := by
  unfold cutoff88Dup cutoff88Nlo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 89 + s := ⟨x - 1 / 89, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 7832 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

lemma cutoff88_Nlo_pos {Z x : ℝ} (hZ : 0 ≤ Z) (hZx : Z * x ≤ 1 / 19)
    (h1 : 1 / 90 ≤ x) (h2 : x ≤ 1 / 88) : 0 < cutoff88Nlo Z x := by
  unfold cutoff88Nlo
  have hx0 : 0 ≤ x := by linarith
  have hz0 : 0 ≤ Z * x := mul_nonneg hZ hx0
  nlinarith [pow_nonneg hz0 2, pow_nonneg hz0 3, mul_nonneg hz0 hx0, pow_nonneg hx0 2,
    pow_nonneg hx0 3, pow_nonneg hx0 4, mul_nonneg (pow_nonneg hz0 2) hx0,
    mul_nonneg (pow_nonneg hz0 3) hx0, mul_nonneg (pow_nonneg hz0 2) (pow_nonneg hx0 2),
    mul_nonneg (pow_nonneg hz0 3) (pow_nonneg hx0 2), mul_nonneg (pow_nonneg hz0 2) (pow_nonneg hx0 3),
    mul_nonneg (pow_nonneg hz0 3) (pow_nonneg hx0 3), mul_nonneg hz0 (pow_nonneg hx0 2),
    mul_nonneg hz0 (pow_nonneg hx0 3)]

lemma cutoff88_Glo_pos {x : ℝ} (h1 : 1 / 90 ≤ x) (h2 : x ≤ 1 / 88) : 0 < cutoff88Glo x := by
  unfold cutoff88Glo
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ x by linarith) 3]


/- The following continuity and power identities adapt the Apache-2.0 baseline by Ezzeri Esa. -/
theorem cutoff88_cyclicB_nonneg (p t : ℝ) : 0 ≤ cyclicB p t := by
  unfold cyclicB
  positivity


theorem cutoff88_cyclicB_rpow {p : ℝ} (hp : 0 < p) (t : ℝ) :
    cyclicB p t ^ p = 2 * |1 - t| ^ p + (2 : ℝ) ^ p := by
  rw [cyclicB, ← Real.rpow_mul (by positivity :
    0 ≤ 2 * |1 - t| ^ p + (2 : ℝ) ^ p), one_div_mul_cancel hp.ne', Real.rpow_one]


theorem cutoff88_continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))


theorem cutoff88_continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const


theorem cutoff88_continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (cutoff88_continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (cutoff88_continuous_cyclicA hp0)).sub
      (continuous_const.mul (cutoff88_continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'


theorem cutoff88_cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (cutoff88_continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)


theorem cutoff88_constructionParameter_power {p : ℝ} (hp : 0 < p) :
    constructionParameter p ^ p = p⁻¹ := by
  rw [constructionParameter, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -(Real.log p * p⁻¹) * p = -Real.log p := by field_simp
  rw [he, Real.exp_neg, Real.exp_log hp]


theorem cutoff88_constructionParameter_deficit {p : ℝ} :
    1 - constructionParameter p ≤ Real.log p * p⁻¹ := by
  have h := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  dsimp [constructionParameter]
  linarith


theorem cutoff88_cyclicB_ge_two {p t : ℝ} (hp : 0 < p) : 2 ≤ cyclicB p t := by
  apply (Real.rpow_le_rpow_iff (by norm_num) (cutoff88_cyclicB_nonneg p t) hp).mp
  rw [cutoff88_cyclicB_rpow hp]
  have hn := Real.rpow_nonneg (abs_nonneg (1 - t)) p
  linarith


lemma cutoff88_parameter_bounds {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    1 / 2 ≤ constructionParameter p ∧ constructionParameter p ≤ 1 := by
  have hl := cutoff88_log_scaled hp (cutoff88_log_upper hp hp') le_rfl
  have he := Real.add_one_le_exp (-(Real.log p * p⁻¹))
  constructor
  · dsimp [constructionParameter]
    linarith [hl.2.2]
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)

lemma cutoff88_cyclicA_exp {p : ℝ} (hp : 88 ≤ p) :
    cyclicA p (constructionParameter p) = Real.exp (Real.log (2 + p⁻¹) * p⁻¹) := by
  rw [cyclicA, cutoff88_constructionParameter_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

lemma cutoff88_log_two_add {x : ℝ} (hx : 0 ≤ x) :
    6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4 ≤ Real.log (2 + x) ∧
      Real.log (2 + x) ≤ 6931471808 / 10 ^ 10 + x / 2 := by
  have hsplit : Real.log (2 + x) = Real.log 2 + Real.log ((2 + x) / 2) := by
    rw [Real.log_div (by positivity) (by norm_num)]
    ring
  have hlo := Real.one_sub_inv_le_log_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hhi := Real.log_le_sub_one_of_pos (show 0 < (2 + x) / 2 by positivity)
  have hinv : 1 - ((2 + x) / 2)⁻¹ = x / (2 + x) := by field_simp; ring
  have hfrac : x / 2 - x ^ 2 / 4 ≤ x / (2 + x) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_nonneg hx 3]
  constructor
  · rw [hsplit]; linarith [Real.log_two_gt_d9]
  · rw [hsplit]; linarith [Real.log_two_lt_d9]

lemma cutoff88_numerator_lower {p Z : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90)
    (hZ : Real.log p < Z) (hZ1 : Z ≤ 4499810 / 1000000) :
    cutoff88Nlo Z p⁻¹ ≤
      3 * cyclicA p (constructionParameter p) -
        (3 : ℝ) ^ (1 / p) * |2 - constructionParameter p| := by
  set x := p⁻¹ with hxdef
  have hi := cutoff88_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := cutoff88_parameter_bounds hp hp'
  have hl := cutoff88_log_scaled hp hZ hZ1
  have hC0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : Real.log (3 : ℝ) < 1098612289 / 10 ^ 9 := by linarith [Real.log_three_lt_d9]
  have hroot : (3 : ℝ) ^ (1 / p) = Real.exp (Real.log 3 * x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hcx0 : 0 ≤ Real.log 3 * x := mul_nonneg hC0 hx0
  have hcx : Real.log 3 * x ≤ 1098612289 / 10 ^ 9 * x := mul_le_mul_of_nonneg_right hC.le hx0
  have hcx1 : 1098612289 / 10 ^ 9 * x ≤ 1 := by nlinarith
  have hR := cutoff88_exp_cubic hcx0 (hcx.trans hcx1)
  have hRmono : 1 + Real.log 3 * x + (Real.log 3 * x) ^ 2 / 2 + 2 * (Real.log 3 * x) ^ 3 / 9 ≤
      1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9 := by
    have h2 := pow_le_pow_left₀ hcx0 hcx 2
    have h3 := pow_le_pow_left₀ hcx0 hcx 3
    linarith
  set z := Real.log p * x with hzdef
  have hz0 : 0 ≤ z := hl.1
  have hzZ : z ≤ Z * x := hl.2.1
  have hz1 : z ≤ 1 := by linarith [hl.2.2]
  have hT := cutoff88_exp_neg_cubic hz0 hz1
  have htdef : constructionParameter p = Real.exp (-z) := rfl
  have habs : |2 - constructionParameter p| = 2 - constructionParameter p :=
    abs_of_nonneg (by linarith [ht.2])
  have hZx1 : Z * x ≤ 1 / 19 := by
    have := mul_le_mul_of_nonneg_right hZ1 hx0
    nlinarith [hi.2]
  have hTmono : 1 + z - z ^ 2 / 2 + 2 * z ^ 3 / 9 ≤
      1 + Z * x - (Z * x) ^ 2 / 2 + 2 * (Z * x) ^ 3 / 9 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hzZ) hz0, mul_nonneg (sub_nonneg.mpr hzZ)
      (mul_nonneg hz0 hz0), mul_nonneg (sub_nonneg.mpr hzZ) (sub_nonneg.mpr hzZ)]
  have hTup : 2 - constructionParameter p ≤
      1 + Z * x - (Z * x) ^ 2 / 2 + 2 * (Z * x) ^ 3 / 9 := by
    rw [htdef]; linarith
  have hT0 : 0 ≤ 2 - constructionParameter p := by linarith [ht.2]
  have hprod := mul_le_mul (hR.trans hRmono) hTup hT0
    (by positivity : (0 : ℝ) ≤ 1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9)
  have ha := cutoff88_log_two_add hx0
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + x)) hx0)
  rw [← cutoff88_cyclicA_exp hp] at hA
  have hy1 : 0 ≤ (6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4) * x := by
    apply mul_nonneg _ hx0; nlinarith
  have hyy := mul_le_mul_of_nonneg_right ha.1 hx0
  have hAmono : 1 + (6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + x / 2 - x ^ 2 / 4) * x) ^ 2 / 2 ≤
      1 + Real.log (2 + x) * x + (Real.log (2 + x) * x) ^ 2 / 2 := by
    have h2 := pow_le_pow_left₀ hy1 hyy 2
    linarith
  rw [hroot, habs]
  unfold cutoff88Nlo
  linarith

lemma cutoff88_denominator_upper {p : ℝ} (hp : 88 ≤ p) :
    6 * cyclicA p (constructionParameter p) - 3 * cyclicB p (constructionParameter p) ≤
      cutoff88Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := cutoff88_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ha := cutoff88_log_two_add hx0
  have ha0 : 0 ≤ Real.log (2 + x) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ Real.log (2 + x) * x := mul_nonneg ha0 hx0
  have hyy := mul_le_mul_of_nonneg_right ha.2 hx0
  have hy1 : (6931471808 / 10 ^ 10 + x / 2) * x ≤ 1 := by nlinarith
  have hE := cutoff88_exp_cubic hy0 (hyy.trans hy1)
  rw [← cutoff88_cyclicA_exp hp] at hE
  have hB := cutoff88_cyclicB_ge_two (t := constructionParameter p) (show 0 < p by linarith)
  have h2 := pow_le_pow_left₀ hy0 hyy 2
  have h3 := pow_le_pow_left₀ hy0 hyy 3
  unfold cutoff88Dup
  linarith

/-- The witness ratio exceeds `20p/43` once its numerator beats the scaled denominator. -/
lemma cutoff88_linear_of_certificate {p Z : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90)
    (hZ : Real.log p < Z) (hZ1 : Z ≤ 4499810 / 1000000)
    (hc : (20 / 43 : ℝ) * cutoff88Dup p⁻¹ < p⁻¹ * cutoff88Nlo Z p⁻¹) :
    (20 / 43 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have ht := cutoff88_parameter_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ constructionParameter p by linarith [ht.1])
  have hn := cutoff88_numerator_lower hp hp' hZ hZ1
  have hd := cutoff88_denominator_upper hp
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (20 / 43 : ℝ) * p < cyclicRatio p (constructionParameter p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 20 / 43 * p by positivity)
    have : p * (p⁻¹ * cutoff88Nlo Z p⁻¹) = cutoff88Nlo Z p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (cutoff88_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)

lemma cutoff88_cyclicConstant_gt_linear {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    (20 / 43 : ℝ) * p < cyclicConstant p := by
  have hi := cutoff88_inverse_bounds hp
  rcases le_total p 89 with h89 | h89
  · exact cutoff88_linear_of_certificate hp hp' (cutoff88_log_upper_low hp h89) (by norm_num)
      (cutoff88_linear_certificate_low (cutoff88_inverse_lower h89 hp) hi.2)
  · have hx : p⁻¹ ≤ 1 / 89 := by simpa using one_div_le_one_div_of_le (by norm_num) h89
    exact cutoff88_linear_of_certificate hp hp' (cutoff88_log_upper hp hp') le_rfl
      (cutoff88_linear_certificate_high (cutoff88_inverse_lower hp' hp) hx)

lemma cutoff88_power_tail {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    (107041 / 300000 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (107041 / 300000 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp

lemma cutoff88_one_sub_exp_neg {y : ℝ} (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    y - y ^ 2 / 2 ≤ 1 - Real.exp (-y) := by
  have h := Real.exp_bound (x := -y) (n := 4) (by simpa [abs_of_nonneg hy]) (by norm_num)
  have he := (abs_sub_le_iff.mp h).1
  norm_num [Finset.sum_range_succ, Nat.factorial, abs_of_nonneg hy] at he
  have h4 : y ^ 4 ≤ y ^ 3 := by nlinarith [mul_nonneg (pow_nonneg hy 3) (sub_nonneg.mpr hy1)]
  nlinarith [pow_nonneg hy 3]

lemma cutoff88_envelope_deficit {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    cutoff88Glo p⁻¹ < 1 - scalarEnvelopeRoot p (107041 / 300000) := by
  have hi := cutoff88_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (107041 / 300000 : ℝ) ^ p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x ^ 2 / 1000 := cutoff88_power_tail hp hp'
  let d := Real.log 2 - Real.log (1 + a)
  have hdLower : Real.log 2 - x ^ 2 / 1000 < d := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have hh := Real.log_nonneg (show 1 ≤ 1 + a by linarith)
    dsimp [d]
    linarith
  have hL : 6931471803 / 10 ^ 10 < Real.log (2 : ℝ) ∧ Real.log 2 < 6931471808 / 10 ^ 10 := by
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hx2 : x ^ 2 / 1000 ≤ 1 / 1000 := by nlinarith [hi.1, hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d * x := mul_nonneg hd0 hi.1.le
  have hdx1 : d * x ≤ 1 := by nlinarith [hL.2]
  have he := cutoff88_one_sub_exp_neg hdx0 hdx1
  have hdx : d * x ≤ 6931471808 / 10 ^ 10 * x := mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hm := mul_lt_mul_of_pos_right (show 6931471803 / 10 ^ 10 - x ^ 2 / 1000 < d by linarith) hi.1
  have hg : scalarEnvelopeRoot p (107041 / 300000) = Real.exp (-(d * x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d, a]
    simp only [one_div, hxdef]
    ring
  rw [hg]
  unfold cutoff88Glo
  linarith

lemma cutoff88_envelope_of_certificate {p Z : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90)
    (hZ : Real.log p < Z) (hZ0 : 0 ≤ Z) (hZ1 : Z ≤ 4499810 / 1000000)
    (hc : (1 - 107041 / 300000 : ℝ) * cutoff88Dup p⁻¹ <
      cutoff88Nlo Z p⁻¹ * (2 * cutoff88Glo p⁻¹)) :
    scalarEnvelope p (107041 / 300000) < cyclicConstant p := by
  have hi := cutoff88_inverse_bounds hp
  have hi' := cutoff88_inverse_lower hp' hp
  have ht := cutoff88_parameter_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ constructionParameter p by linarith [ht.1])
  have hn := cutoff88_numerator_lower hp hp' hZ hZ1
  have hd := cutoff88_denominator_upper hp
  have hg := cutoff88_envelope_deficit hp hp'
  have hZx : Z * p⁻¹ ≤ 1 / 19 := by
    have := mul_le_mul_of_nonneg_right hZ1 hi.1.le
    nlinarith [hi.2]
  have hN0 := cutoff88_Nlo_pos hZ0 hZx hi' hi.2
  have hG0 := cutoff88_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (107041 / 300000)) := by linarith
  have hr : scalarEnvelope p (107041 / 300000) < cyclicRatio p (constructionParameter p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (107041 / 300000 : ℝ)) * cutoff88Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < cutoff88Nlo Z p⁻¹ * (2 * cutoff88Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (constructionParameter p) -
          (3 : ℝ) ^ (1 / p) * |2 - constructionParameter p|) *
          (2 * (1 - scalarEnvelopeRoot p (107041 / 300000))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (cutoff88_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)

lemma cutoff88_envelope_lt {p : ℝ} (hp : 88 ≤ p) (hp' : p ≤ 90) :
    scalarEnvelope p (107041 / 300000) < cyclicConstant p := by
  have hi := cutoff88_inverse_bounds hp
  rcases le_total p 89 with h89 | h89
  · exact cutoff88_envelope_of_certificate hp hp' (cutoff88_log_upper_low hp h89)
      (by norm_num) (by norm_num)
      (cutoff88_envelope_certificate_low (cutoff88_inverse_lower h89 hp) hi.2)
  · have hx : p⁻¹ ≤ 1 / 89 := by simpa using one_div_le_one_div_of_le (by norm_num) h89
    exact cutoff88_envelope_of_certificate hp hp' (cutoff88_log_upper hp hp') (by norm_num) le_rfl
      (cutoff88_envelope_certificate_high (cutoff88_inverse_lower hp' hp) hx)


/-! ### Scalar estimates on the window `87 ≤ p ≤ 88`

On this window the witness `p^{-1/p}` is replaced by
`w_p = (3/(4p))^{1/p}`, which lies closer to the maximiser of the cyclic ratio.
Its `p`-th power is still explicit, `w_p^p = 3/(4p)`. Each comparison is closed by
an exact polynomial certificate in `x = p⁻¹ ∈ [1/88, 1/87]`. -/

/-- The improved cyclic witness `(3/(4p))^{1/p}`. -/
noncomputable def cutoff87Witness (p : ℝ) : ℝ :=
  Real.exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))

lemma cutoff87_inverse_bounds {p : ℝ} (hp : 87 ≤ p) :
    0 < p⁻¹ ∧ p⁻¹ ≤ 1 / 87 := by
  exact ⟨inv_pos.mpr (by linarith), by simpa using one_div_le_one_div_of_le (by norm_num) hp⟩

lemma cutoff87_inverse_lower {p : ℝ} (hp' : p ≤ 88) (hp : 87 ≤ p) : 1 / 88 ≤ p⁻¹ := by
  rw [← one_div]
  exact one_div_le_one_div_of_le (by linarith) hp'

lemma cutoff87_log_eightyeight : Real.log (88 : ℝ) < 447760 / 100000 := by
  have heq : Real.log (90 : ℝ) = Real.log 2 + 2 * Real.log 3 + Real.log 5 := by
    rw [show (90 : ℝ) = 2 * (3 ^ 2) * 5 by norm_num,
      Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    ring
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 88 / 90 by norm_num)
  rw [Real.log_div (by norm_num) (by norm_num), heq] at h
  linarith [Real.log_two_lt_d9, Real.log_three_lt_d9, Real.log_five_lt_d9]

lemma cutoff87_log_three_quarters :
    -2876820737 / 10 ^ 10 < Real.log (3 / 4 : ℝ) ∧ Real.log (3 / 4 : ℝ) < 0 := by
  have heq : Real.log (3 / 4 : ℝ) = Real.log 3 - 2 * Real.log 2 := by
    rw [Real.log_div (by norm_num) (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    ring
  exact ⟨by rw [heq]; linarith [Real.log_two_lt_d9, Real.log_three_gt_d9],
    Real.log_neg (by norm_num) (by norm_num)⟩

lemma cutoff87_scaled {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    0 ≤ (Real.log p - Real.log (3 / 4)) * p⁻¹ ∧
      (Real.log p - Real.log (3 / 4)) * p⁻¹ ≤ 47652821 / 10 ^ 7 * p⁻¹ ∧
      (Real.log p - Real.log (3 / 4)) * p⁻¹ < 1 / 18 := by
  have hi := cutoff87_inverse_bounds hp
  have hl := (Real.log_le_log (by linarith) hp').trans_lt cutoff87_log_eightyeight
  have hl0 : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hk := cutoff87_log_three_quarters
  have hZ : Real.log p - Real.log (3 / 4) ≤ 47652821 / 10 ^ 7 := by linarith [hk.1]
  have hZ0 : 0 ≤ Real.log p - Real.log (3 / 4) := by linarith [hk.2]
  refine ⟨mul_nonneg hZ0 hi.1.le, mul_le_mul_of_nonneg_right hZ hi.1.le, ?_⟩
  nlinarith [mul_le_mul_of_nonneg_right hZ hi.1.le]

lemma cutoff87_witness_power {p : ℝ} (hp : 0 < p) :
    cutoff87Witness p ^ p = 3 / 4 * p⁻¹ := by
  rw [cutoff87Witness, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have he : -((Real.log p - Real.log (3 / 4)) * p⁻¹) * p = Real.log (3 / 4) - Real.log p := by
    field_simp
    ring
  rw [he, Real.exp_sub, Real.exp_log hp, Real.exp_log (by norm_num)]
  field_simp

lemma cutoff87_witness_bounds {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    1 / 2 ≤ cutoff87Witness p ∧ cutoff87Witness p ≤ 1 := by
  have hl := cutoff87_scaled hp hp'
  have he := Real.add_one_le_exp (-((Real.log p - Real.log (3 / 4)) * p⁻¹))
  constructor
  · dsimp [cutoff87Witness]
    linarith [hl.2.2]
  · exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr hl.1)

lemma cutoff87_cyclicA_exp {p : ℝ} (hp : 87 ≤ p) :
    cyclicA p (cutoff87Witness p) =
      Real.exp (Real.log (2 + 3 / 4 * p⁻¹) * p⁻¹) := by
  rw [cyclicA, cutoff87_witness_power (by linarith), add_comm,
    Real.rpow_def_of_pos (by positivity)]
  simp only [one_div]

/-- Lower bound for the cyclic numerator at the improved witness. -/
noncomputable def cutoff87Nlo (x : ℝ) : ℝ :=
  3 * (1 + (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x) ^ 2 / 2) -
    (1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9) *
      (1 + 47652821 / 10 ^ 7 * x - (47652821 / 10 ^ 7 * x) ^ 2 / 2 +
        2 * (47652821 / 10 ^ 7 * x) ^ 3 / 9)

/-- Upper bound for the cyclic denominator at the improved witness. -/
noncomputable def cutoff87Dup (x : ℝ) : ℝ :=
  6 * ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x +
    ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x) ^ 2 / 2 +
    2 * ((6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x) ^ 3 / 9)

/-- Lower bound for the envelope deficit. -/
noncomputable def cutoff87Glo (x : ℝ) : ℝ :=
  (6931471803 / 10 ^ 10 - x ^ 2 / 1000) * x - (6931471808 / 10 ^ 10 * x) ^ 2 / 2

set_option maxHeartbeats 4000000 in
lemma cutoff87_envelope_certificate {x : ℝ} (h1 : 1 / 88 ≤ x) (h2 : x ≤ 1 / 87) :
    (1 - 5351 / 15000 : ℝ) * cutoff87Dup x < cutoff87Nlo x * (2 * cutoff87Glo x) := by
  unfold cutoff87Dup cutoff87Nlo cutoff87Glo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 88 + s := ⟨x - 1 / 88, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 7656 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8, pow_nonneg hs 9, pow_nonneg hs 10,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

set_option maxHeartbeats 4000000 in
lemma cutoff87_linear_certificate {x : ℝ} (h1 : 1 / 88 ≤ x) (h2 : x ≤ 1 / 87) :
    (20 / 43 : ℝ) * cutoff87Dup x < x * cutoff87Nlo x := by
  unfold cutoff87Dup cutoff87Nlo
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 ≤ s ∧ x = 1 / 88 + s := ⟨x - 1 / 88, by linarith, by ring⟩
  have hs2 : s ≤ 1 / 7656 := by linarith
  nlinarith [mul_nonneg hs hs, mul_nonneg (mul_nonneg hs hs) hs, pow_nonneg hs 4, pow_nonneg hs 5,
    pow_nonneg hs 6, pow_nonneg hs 7, pow_nonneg hs 8,
    mul_nonneg hs (sub_nonneg.mpr hs2)]

lemma cutoff87_Nlo_pos {x : ℝ} (h1 : 1 / 88 ≤ x) (h2 : x ≤ 1 / 87) : 0 < cutoff87Nlo x := by
  have h := cutoff87_linear_certificate h1 h2
  have hD : 0 < cutoff87Dup x := by
    unfold cutoff87Dup
    have hx : 0 < x := by linarith
    positivity
  nlinarith

lemma cutoff87_Glo_pos {x : ℝ} (h1 : 1 / 88 ≤ x) (h2 : x ≤ 1 / 87) : 0 < cutoff87Glo x := by
  unfold cutoff87Glo
  nlinarith [pow_nonneg (show (0 : ℝ) ≤ x by linarith) 3]

lemma cutoff87_numerator_lower {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    cutoff87Nlo p⁻¹ ≤
      3 * cyclicA p (cutoff87Witness p) -
        (3 : ℝ) ^ (1 / p) * |2 - cutoff87Witness p| := by
  set x := p⁻¹ with hxdef
  have hi := cutoff87_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have ht := cutoff87_witness_bounds hp hp'
  have hl := cutoff87_scaled hp hp'
  have hC0 : 0 ≤ Real.log (3 : ℝ) := Real.log_nonneg (by norm_num)
  have hC : Real.log (3 : ℝ) < 1098612289 / 10 ^ 9 := by linarith [Real.log_three_lt_d9]
  have hroot : (3 : ℝ) ^ (1 / p) = Real.exp (Real.log 3 * x) := by
    rw [Real.rpow_def_of_pos (by norm_num), one_div]
  have hcx0 : 0 ≤ Real.log 3 * x := mul_nonneg hC0 hx0
  have hcx : Real.log 3 * x ≤ 1098612289 / 10 ^ 9 * x := mul_le_mul_of_nonneg_right hC.le hx0
  have hcx1 : 1098612289 / 10 ^ 9 * x ≤ 1 := by nlinarith
  have hR := cutoff88_exp_cubic hcx0 (hcx.trans hcx1)
  have hRmono : 1 + Real.log 3 * x + (Real.log 3 * x) ^ 2 / 2 + 2 * (Real.log 3 * x) ^ 3 / 9 ≤
      1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9 := by
    have h2 := pow_le_pow_left₀ hcx0 hcx 2
    have h3 := pow_le_pow_left₀ hcx0 hcx 3
    linarith
  set z := (Real.log p - Real.log (3 / 4)) * x with hzdef
  have hz0 : 0 ≤ z := hl.1
  have hzZ : z ≤ 47652821 / 10 ^ 7 * x := hl.2.1
  have hz1 : z ≤ 1 := by linarith [hl.2.2]
  have hT := cutoff88_exp_neg_cubic hz0 hz1
  have htdef : cutoff87Witness p = Real.exp (-z) := rfl
  have habs : |2 - cutoff87Witness p| = 2 - cutoff87Witness p :=
    abs_of_nonneg (by linarith [ht.2])
  have hTmono : 1 + z - z ^ 2 / 2 + 2 * z ^ 3 / 9 ≤
      1 + 47652821 / 10 ^ 7 * x - (47652821 / 10 ^ 7 * x) ^ 2 / 2 +
        2 * (47652821 / 10 ^ 7 * x) ^ 3 / 9 := by
    have hZ1 : 47652821 / 10 ^ 7 * x ≤ 1 / 18 := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hzZ) hz0, mul_nonneg (sub_nonneg.mpr hzZ)
      (mul_nonneg hz0 hz0), mul_nonneg (sub_nonneg.mpr hzZ) (sub_nonneg.mpr hzZ)]
  have hTup : 2 - cutoff87Witness p ≤
      1 + 47652821 / 10 ^ 7 * x - (47652821 / 10 ^ 7 * x) ^ 2 / 2 +
        2 * (47652821 / 10 ^ 7 * x) ^ 3 / 9 := by
    rw [htdef]; linarith
  have hT0 : 0 ≤ 2 - cutoff87Witness p := by linarith [ht.2]
  have hprod := mul_le_mul (hR.trans hRmono) hTup hT0
    (by positivity : (0 : ℝ) ≤ 1 + 1098612289 / 10 ^ 9 * x + (1098612289 / 10 ^ 9 * x) ^ 2 / 2 +
        2 * (1098612289 / 10 ^ 9 * x) ^ 3 / 9)
  have hkx0 : 0 ≤ 3 / 4 * x := by positivity
  have ha := cutoff88_log_two_add hkx0
  have hA := Real.quadratic_le_exp_of_nonneg
    (mul_nonneg (Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 + 3 / 4 * x)) hx0)
  rw [← cutoff87_cyclicA_exp hp] at hA
  have hy1 : 0 ≤ (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x := by
    apply mul_nonneg _ hx0; nlinarith
  have hyy := mul_le_mul_of_nonneg_right ha.1 hx0
  have hAmono : 1 + (6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x +
      ((6931471803 / 10 ^ 10 + 3 / 4 * x / 2 - (3 / 4 * x) ^ 2 / 4) * x) ^ 2 / 2 ≤
      1 + Real.log (2 + 3 / 4 * x) * x + (Real.log (2 + 3 / 4 * x) * x) ^ 2 / 2 := by
    have h2 := pow_le_pow_left₀ hy1 hyy 2
    linarith
  rw [hroot, habs]
  unfold cutoff87Nlo
  linarith

lemma cutoff87_denominator_upper {p : ℝ} (hp : 87 ≤ p) :
    6 * cyclicA p (cutoff87Witness p) - 3 * cyclicB p (cutoff87Witness p) ≤
      cutoff87Dup p⁻¹ := by
  set x := p⁻¹ with hxdef
  have hi := cutoff87_inverse_bounds hp
  have hx0 : 0 ≤ x := hi.1.le
  have hkx0 : 0 ≤ 3 / 4 * x := by positivity
  have ha := cutoff88_log_two_add hkx0
  have ha0 : 0 ≤ Real.log (2 + 3 / 4 * x) := Real.log_nonneg (by linarith)
  have hy0 : 0 ≤ Real.log (2 + 3 / 4 * x) * x := mul_nonneg ha0 hx0
  have hyy := mul_le_mul_of_nonneg_right ha.2 hx0
  have hy1 : (6931471808 / 10 ^ 10 + 3 / 4 * x / 2) * x ≤ 1 := by nlinarith
  have hE := cutoff88_exp_cubic hy0 (hyy.trans hy1)
  rw [← cutoff87_cyclicA_exp hp] at hE
  have hB := cutoff88_cyclicB_ge_two (t := cutoff87Witness p) (show 0 < p by linarith)
  have h2 := pow_le_pow_left₀ hy0 hyy 2
  have h3 := pow_le_pow_left₀ hy0 hyy 3
  unfold cutoff87Dup
  linarith

lemma cutoff87_cyclicConstant_gt_linear {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    (20 / 43 : ℝ) * p < cyclicConstant p := by
  have hp0 : 0 < p := by linarith
  have hi := cutoff87_inverse_bounds hp
  have hi' := cutoff87_inverse_lower hp' hp
  have ht := cutoff87_witness_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ cutoff87Witness p by linarith [ht.1])
  have hn := cutoff87_numerator_lower hp hp'
  have hd := cutoff87_denominator_upper hp
  have hc := cutoff87_linear_certificate hi' hi.2
  have hpi : p * p⁻¹ = 1 := mul_inv_cancel₀ hp0.ne'
  have hr : (20 / 43 : ℝ) * p < cyclicRatio p (cutoff87Witness p) := by
    rw [cyclicRatio, lt_div_iff₀ hD]
    have hcp := mul_lt_mul_of_pos_left hc hp0
    have hdp := mul_le_mul_of_nonneg_left hd (show (0 : ℝ) ≤ 20 / 43 * p by positivity)
    have : p * (p⁻¹ * cutoff87Nlo p⁻¹) = cutoff87Nlo p⁻¹ := by
      rw [← mul_assoc, hpi, one_mul]
    nlinarith
  exact hr.trans_le (cutoff88_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)

lemma cutoff87_power_tail {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    (5351 / 15000 : ℝ) ^ p < (p⁻¹) ^ 2 / 1000 := by
  have hp0 : 0 < p := by linarith
  have h := one_add_mul_self_le_rpow_one_add (s := (1 : ℝ)) (by norm_num)
    (show 1 ≤ p - 20 by linarith)
  norm_num at h
  have heq : (2 : ℝ) ^ p = 1048576 * (2 : ℝ) ^ (p - 20) := by
    rw [show p = (p - 20) + 20 by ring, Real.rpow_add (by norm_num)]
    norm_num
    ring
  have htwo : 1000 * p ^ 2 < (2 : ℝ) ^ p := by rw [heq]; nlinarith
  calc
    (5351 / 15000 : ℝ) ^ p ≤ (1 / 2 : ℝ) ^ p :=
      Real.rpow_le_rpow (by norm_num) (by norm_num) hp0.le
    _ = ((2 : ℝ) ^ p)⁻¹ := by rw [one_div, Real.inv_rpow (by norm_num)]
    _ < (1000 * p ^ 2)⁻¹ := inv_strictAnti₀ (by positivity) htwo
    _ = (p⁻¹) ^ 2 / 1000 := by field_simp

lemma cutoff87_envelope_deficit {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    cutoff87Glo p⁻¹ < 1 - scalarEnvelopeRoot p (5351 / 15000) := by
  have hi := cutoff87_inverse_bounds hp
  set x := p⁻¹ with hxdef
  let a := (5351 / 15000 : ℝ) ^ p
  have ha0 : 0 ≤ a := Real.rpow_nonneg (by norm_num) p
  have ha : a < x ^ 2 / 1000 := cutoff87_power_tail hp hp'
  let d := Real.log 2 - Real.log (1 + a)
  have hdLower : Real.log 2 - x ^ 2 / 1000 < d := by
    have hh := Real.log_le_sub_one_of_pos (show 0 < 1 + a by positivity)
    dsimp [d]
    linarith
  have hdUpper : d ≤ Real.log 2 := by
    have hh := Real.log_nonneg (show 1 ≤ 1 + a by linarith)
    dsimp [d]
    linarith
  have hL : 6931471803 / 10 ^ 10 < Real.log (2 : ℝ) ∧ Real.log 2 < 6931471808 / 10 ^ 10 := by
    constructor <;> linarith [Real.log_two_gt_d9, Real.log_two_lt_d9]
  have hx2 : x ^ 2 / 1000 ≤ 1 / 1000 := by nlinarith [hi.1, hi.2]
  have hd0 : 0 ≤ d := by linarith [hL.1]
  have hdx0 : 0 ≤ d * x := mul_nonneg hd0 hi.1.le
  have hdx1 : d * x ≤ 1 := by nlinarith [hL.2]
  have he := cutoff88_one_sub_exp_neg hdx0 hdx1
  have hdx : d * x ≤ 6931471808 / 10 ^ 10 * x := mul_le_mul_of_nonneg_right (by linarith) hi.1.le
  have hsq := pow_le_pow_left₀ hdx0 hdx 2
  have hm := mul_lt_mul_of_pos_right (show 6931471803 / 10 ^ 10 - x ^ 2 / 1000 < d by linarith) hi.1
  have hg : scalarEnvelopeRoot p (5351 / 15000) = Real.exp (-(d * x)) := by
    rw [scalarEnvelopeRoot, Real.rpow_def_of_pos (by positivity),
      Real.log_div (by positivity) (by norm_num)]
    congr 1
    dsimp [d, a]
    simp only [one_div, hxdef]
    ring
  rw [hg]
  unfold cutoff87Glo
  linarith

lemma cutoff87_envelope_lt {p : ℝ} (hp : 87 ≤ p) (hp' : p ≤ 88) :
    scalarEnvelope p (5351 / 15000) < cyclicConstant p := by
  have hi := cutoff87_inverse_bounds hp
  have hi' := cutoff87_inverse_lower hp' hp
  have ht := cutoff87_witness_bounds hp hp'
  have hD := cyclic_denominator_pos (show 1 < p by linarith)
    (show 0 ≤ cutoff87Witness p by linarith [ht.1])
  have hn := cutoff87_numerator_lower hp hp'
  have hd := cutoff87_denominator_upper hp
  have hg := cutoff87_envelope_deficit hp hp'
  have hc := cutoff87_envelope_certificate hi' hi.2
  have hN0 := cutoff87_Nlo_pos hi' hi.2
  have hG0 := cutoff87_Glo_pos hi' hi.2
  have henvD : 0 < 2 * (1 - scalarEnvelopeRoot p (5351 / 15000)) := by linarith
  have hr : scalarEnvelope p (5351 / 15000) < cyclicRatio p (cutoff87Witness p) := by
    rw [scalarEnvelope, cyclicRatio, div_lt_div_iff₀ henvD hD]
    calc
      _ ≤ (1 - (5351 / 15000 : ℝ)) * cutoff87Dup p⁻¹ :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ < cutoff87Nlo p⁻¹ * (2 * cutoff87Glo p⁻¹) := hc
      _ ≤ (3 * cyclicA p (cutoff87Witness p) -
          (3 : ℝ) ^ (1 / p) * |2 - cutoff87Witness p|) *
          (2 * (1 - scalarEnvelopeRoot p (5351 / 15000))) :=
        mul_le_mul hn (by linarith) (by linarith) (hN0.le.trans hn)
  exact hr.trans_le (cutoff88_cyclicRatio_le_constant (by linarith) ⟨ht.1, by linarith [ht.2]⟩)


end HlawkaSchatten.DiagonalConstruction





/- Adapted from the Apache-2.0 HlawkaSchatten development by Ezzeri Esa. -/
set_option maxHeartbeats 800000
namespace HlawkaSchatten.DiagonalConstruction.Cutoff87Curvature
open HlawkaSchatten.DiagonalConstruction

section Basic
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i

theorem lpNorm_rpow {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x ^ p = ∑ i, ‖x i‖ ^ p := by
  unfold lpNorm
  rw [← Real.rpow_mul (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
  rw [one_div_mul_cancel hp.ne', Real.rpow_one]

theorem lpNorm_eq_zero_iff {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hs : (∑ i, ‖x i‖ ^ p) = 0 := by
      rw [← lpNorm_rpow hp x, h, Real.zero_rpow hp.ne']
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ Finset.univ) ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)).mp hs
    funext i
    exact norm_eq_zero.mp ((Real.rpow_eq_zero (norm_nonneg (x i)) hp.ne').mp
      (hi i (Finset.mem_univ i)))
  · rintro rfl
    exact lpNorm_zero hp

theorem lpNorm_pos {p : ℝ} (hp : 0 < p) {x : ι → E} (hx : x ≠ 0) :
    0 < lpNorm p x :=
  lt_of_le_of_ne (lpNorm_nonneg p x) (Ne.symm ((lpNorm_eq_zero_iff hp x).not.mpr hx))

theorem continuous_lpNorm {p : ℝ} (hp : 0 < p) :
    Continuous (lpNorm p : (ι → E) → ℝ) := by
  exact (continuous_finsetSum _ fun i _ ↦
    (continuous_apply i).norm.rpow_const (fun _ ↦ Or.inr hp.le)).rpow_const
      (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem lpNorm_le_card_root_mul {p M : ℝ} (hp : 0 < p) (hM : 0 ≤ M)
    (x : ι → E) (hx : ∀ i, ‖x i‖ ≤ M) :
    lpNorm p x ≤ (Fintype.card ι : ℝ) ^ (1 / p) * M := by
  have hsum : (∑ i, ‖x i‖ ^ p) ≤ (Fintype.card ι : ℝ) * M ^ p := by
    calc
      _ ≤ ∑ _ : ι, M ^ p :=
        Finset.sum_le_sum fun i _ ↦ Real.rpow_le_rpow (norm_nonneg _) (hx i) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg hM _),
    ← Real.rpow_mul hM, mul_one_div_cancel hp.ne', Real.rpow_one] at h
  exact h

end Basic

section Norm
variable {ι : Type*} [Fintype ι]
theorem powerSum_nonneg (p : ℝ) (v : ι → ℝ) : 0 ≤ powerSum p v :=
  Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p

theorem powerSum_eq_lpNorm_rpow {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v = lpNorm p v ^ p := by
  rw [lpNorm_rpow hp]
  rfl

theorem powerSum_pos {p : ℝ} (hp : 0 < p) {v : ι → ℝ} (hv : v ≠ 0) : 0 < powerSum p v := by
  rw [powerSum_eq_lpNorm_rpow hp]
  exact Real.rpow_pos_of_pos (lpNorm_pos hp hv) p

omit [Fintype ι] in
private theorem abs_rpow_mul_sq {q : ℝ} (hq : 0 < q) (x : ℝ) :
    |x| ^ q * x ^ 2 = |x| ^ (q + 2) := by
  by_cases hx : x = 0
  · simp [hx, hq.ne', show q + 2 ≠ 0 by linarith]
  · rw [← sq_abs, ← Real.rpow_two, ← Real.rpow_add (abs_pos.mpr hx)]

theorem powerQuad_self {p : ℝ} (hp : 2 < p) (v : ι → ℝ) :
    powerQuad p v v = powerSum p v := by
  unfold powerQuad powerSum
  apply Finset.sum_congr rfl
  intro i _
  simpa only [sub_add_cancel] using abs_rpow_mul_sq (by linarith : 0 < p - 2) (v i)

theorem powerResidual_eq {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerResidual p v h a = powerQuad p v h - 2 * a * powerPair p v h + a ^ 2 * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerResidual, powerQuad, powerPair, Finset.mul_sum, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem powerResidual_radial {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) :
    powerResidual p v h (radialCoefficient p v h) =
      powerQuad p v h - powerPair p v h ^ 2 / powerSum p v := by
  rw [powerResidual_eq hp, radialCoefficient]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

theorem powerResidual_min {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    powerResidual p v h (radialCoefficient p v h) ≤ powerResidual p v h a := by
  have hS := powerSum_pos (by linarith : 0 < p) hv
  rw [powerResidual_radial hp v h hv, powerResidual_eq hp]
  have hn := mul_nonneg hS.le (sq_nonneg (a - powerPair p v h / powerSum p v))
  have hmul : powerSum p v * (powerPair p v h / powerSum p v) = powerPair p v h :=
    mul_div_cancel₀ _ hS.ne'
  have hmul2 : powerSum p v * (powerPair p v h / powerSum p v) ^ 2 =
      powerPair p v h ^ 2 / powerSum p v := by field_simp
  nlinarith [congrArg (fun x : ℝ ↦ a * x) hmul]

theorem powerResidual_nonneg (p : ℝ) (v h : ι → ℝ) (a : ℝ) : 0 ≤ powerResidual p v h a :=
  Finset.sum_nonneg fun i _ ↦ mul_nonneg
    (Real.rpow_nonneg (abs_nonneg (v i)) (p - 2)) (sq_nonneg (h i - a * v i))

theorem normHessian_nonneg {p : ℝ} (hp : 1 ≤ p) (v h : ι → ℝ) : 0 ≤ normHessian p v h :=
  mul_nonneg (mul_nonneg (sub_nonneg.mpr hp) (Real.rpow_nonneg (powerSum_nonneg p v) _))
    (powerResidual_nonneg p v h _)

theorem normHessian_le_residual {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v h ≤ (p - 1) * powerSum p v ^ (1 / p - 1) * powerResidual p v h a := by
  exact mul_le_mul_of_nonneg_left (powerResidual_min hp v h hv a)
    (mul_nonneg (by linarith) (Real.rpow_nonneg (powerSum_nonneg p v) _))

omit [Fintype ι] in
private theorem hasDerivAt_abs_power_slope {p : ℝ} (hp : 4 < p) (x : ℝ) :
    HasDerivAt (fun x : ℝ ↦ |x| ^ (p - 2) * x) ((p - 1) * |x| ^ (p - 2)) x := by
  have h := (hasDerivAt_abs_rpow x (by linarith : 1 < p - 2)).mul (hasDerivAt_id x)
  have heq : ((p - 2) * |x| ^ (p - 2 - 2) * x) * x + |x| ^ (p - 2) * 1 =
      (p - 1) * |x| ^ (p - 2) := by
    have hh := abs_rpow_mul_sq (by linarith : 0 < p - 2 - 2) x
    have hcancel : p - 2 - 2 + 2 = p - 2 := by ring
    rw [hcancel] at hh
    nlinarith
  convert! h using 1
  simpa only [id_eq] using heq.symm

theorem hasDerivAt_powerSum_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerSum p (v + s • h))
      (p * powerPair p (v + t • h) h) t := by
  have hi (i : ι) : HasDerivAt (fun s : ℝ ↦ |v i + s * h i| ^ p)
      (p * |v i + t * h i| ^ (p - 2) * (v i + t * h i) * h i) t := by
    simpa only [one_mul, id_eq, Function.comp_def] using
      (hasDerivAt_abs_rpow _ hp).comp t (((hasDerivAt_id t).mul_const (h i)).const_add (v i))
  simpa only [powerSum, powerPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    mul_assoc] using HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

theorem hasDerivAt_powerPair_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ powerPair p (v + s • h) h)
      ((p - 1) * powerQuad p (v + t • h) h) t := by
  have hi (i : ι) := ((hasDerivAt_abs_power_slope hp (v i + t * h i)).comp t
    (((hasDerivAt_id t).mul_const (h i)).const_add (v i))).mul_const (h i)
  simpa only [powerPair, powerQuad, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
    pow_two, mul_assoc, Function.comp_def, id_eq, one_mul] using
      HasDerivAt.fun_sum (u := Finset.univ) (fun i _ ↦ hi i)

theorem hasDerivAt_lpNorm_line {p : ℝ} (hp : 1 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ lpNorm p (v + s • h)) (normSlope p (v + t • h) h) t := by
  have hp0 := zero_lt_one.trans hp
  have hh := (hasDerivAt_powerSum_line hp v h t).rpow_const (p := 1 / p)
    (Or.inl (powerSum_pos hp0 hv).ne')
  have he : p * powerPair p (v + t • h) h * (1 / p) * powerSum p (v + t • h) ^ (1 / p - 1) =
      normSlope p (v + t • h) h := by
    unfold normSlope
    field_simp
  convert hh using 1
  · rfl
  · exact he.symm

theorem hasDerivAt_normSlope_line {p : ℝ} (hp : 4 < p) (v h : ι → ℝ) (t : ℝ)
    (hv : v + t • h ≠ 0) :
    HasDerivAt (fun s : ℝ ↦ normSlope p (v + s • h) h) (normHessian p (v + t • h) h) t := by
  have hp0 : 0 < p := by linarith
  have hS := powerSum_pos hp0 hv
  have hh := ((hasDerivAt_powerSum_line (by linarith) v h t).rpow_const (p := 1 / p - 1)
    (Or.inl hS.ne')).mul (hasDerivAt_powerPair_line hp v h t)
  have hpow : powerSum p (v + t • h) ^ (1 / p - 1 - 1) =
      powerSum p (v + t • h) ^ (1 / p - 1) / powerSum p (v + t • h) := by
    rw [Real.rpow_sub hS, Real.rpow_one]
  have he : (p * powerPair p (v + t • h) h * (1 / p - 1) *
      powerSum p (v + t • h) ^ (1 / p - 1 - 1)) * powerPair p (v + t • h) h +
      powerSum p (v + t • h) ^ (1 / p - 1) * ((p - 1) * powerQuad p (v + t • h) h) =
        normHessian p (v + t • h) h := by
    rw [normHessian, powerResidual_radial (by linarith) _ _ hv, hpow]
    field_simp
    ring
  rwa [he] at hh

theorem powerPair_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (a : ℝ) :
    powerPair p v (h - a • v) = powerPair p v h - a * powerSum p v := by
  rw [← powerQuad_self hp v]
  simp only [powerPair, powerQuad, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ ↦ by ring

theorem normHessian_sub_smul {p : ℝ} (hp : 2 < p) (v h : ι → ℝ) (hv : v ≠ 0) (a : ℝ) :
    normHessian p v (h - a • v) = normHessian p v h := by
  simp only [normHessian, powerResidual_radial hp v _ hv, powerPair_sub_smul hp]
  congr 1
  have hquad : powerQuad p v (h - a • v) = powerResidual p v h a := rfl
  rw [hquad, powerResidual_eq hp]
  field_simp [(powerSum_pos (by linarith : 0 < p) hv).ne']
  ring

theorem powerSum_root_pred {p : ℝ} (hp : 0 < p) (v : ι → ℝ) :
    powerSum p v ^ (1 / p - 1) = (lpNorm p v ^ (p - 1))⁻¹ := by
  rw [powerSum_eq_lpNorm_rpow hp, ← Real.rpow_mul (lpNorm_nonneg p v),
    show p * (1 / p - 1) = -(p - 1) by field_simp; ring,
    Real.rpow_neg (lpNorm_nonneg p v)]

theorem normHessian_eq_div {p : ℝ} (hp : 0 < p) (v h : ι → ℝ) :
    normHessian p v h = (p - 1) / lpNorm p v ^ (p - 1) *
      powerResidual p v h (radialCoefficient p v h) := by
  rw [normHessian, powerSum_root_pred hp]
  rfl

end Norm
theorem euclideanSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ euclideanSq v :=
  Finset.sum_nonneg fun i _ ↦ sq_nonneg (v i)

theorem frobeniusSq_nonneg (X : Triple) : 0 ≤ frobeniusSq X :=
  Finset.sum_nonneg fun j _ ↦ euclideanSq_nonneg (X j)

theorem euclideanSq_add_le (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (u i - v i)]

theorem euclideanSq_neg (v : Fin 3 → ℝ) : euclideanSq (-v) = euclideanSq v := by
  simp [euclideanSq]

theorem euclideanSq_sub_le (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ 2 * euclideanSq u + 2 * euclideanSq v := by
  simpa only [sub_eq_add_neg, euclideanSq_neg] using euclideanSq_add_le u (-v)

theorem euclideanSq_smul (a : ℝ) (v : Fin 3 → ℝ) :
    euclideanSq (a • v) = a ^ 2 * euclideanSq v := by
  simp only [euclideanSq, Pi.smul_apply, smul_eq_mul, mul_pow, Finset.mul_sum]

theorem euclideanSq_total_le (X : Triple) : euclideanSq (totalTriple X) ≤ 3 * frobeniusSq X := by
  have hi (i : Fin 3) : ((∑ j, X j i) ^ 2) ≤ 3 * ∑ j, (X j i) ^ 2 := by
    simpa using Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) (fun j ↦ X j i)
  calc
    _ ≤ ∑ i, 3 * ∑ j, (X j i) ^ 2 := Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by
      simp only [frobeniusSq, euclideanSq, ← Finset.mul_sum]
      rw [Finset.sum_comm]

theorem euclideanSq_center_lower (a : Fin 3 → ℝ) :
    euclideanSq a ≤ euclideanSq (applyTriple cyclicCenter a) := by
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin 3 ↦ (1 : ℝ)) a
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hc
  have he : euclideanSq (applyTriple cyclicCenter a) = 4 * euclideanSq a - (∑ i, a i) ^ 2 := by
    have heq : applyTriple cyclicCenter a =
        ![-a 0 + a 1 + a 2, a 0 - a 1 + a 2, a 0 + a 1 - a 2] := by
      ext i
      fin_cases i <;>
        norm_num [applyTriple, cyclicCenter, Fin.sum_univ_three, Fin.ext_iff] <;> ring!
    rw [heq]
    simp only [euclideanSq, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    ring!
  rw [he]
  change (∑ i, a i) ^ 2 ≤ 3 * euclideanSq a at hc
  linarith

theorem euclideanSq_perturbation_upper {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    euclideanSq (applyTriple (X - cyclicCenter) a) ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a := by
  have hrow (i : Fin 3) : (∑ j, (X j i - cyclicCenter j i) ^ 2) ≤ 3 * (19 / 100 : ℝ) ^ 2 := by
    calc
      _ ≤ ∑ _ : Fin 3, (19 / 100 : ℝ) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hX j i)
      _ = _ := by simp
  have hi (i : Fin 3) : (∑ j, a j * (X j i - cyclicCenter j i)) ^ 2 ≤
      euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) := by
    exact (Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a (fun j ↦ X j i - cyclicCenter j i)).trans
      (mul_le_mul_of_nonneg_left (hrow i) (euclideanSq_nonneg a))
  calc
    _ ≤ ∑ _ : Fin 3, euclideanSq a * (3 * (19 / 100 : ℝ) ^ 2) :=
      Finset.sum_le_sum fun i _ ↦ hi i
    _ = _ := by simp; ring

/-- Uniform invertibility, expressed entirely with sums of squares. -/
theorem euclideanSq_apply_lower {X : Triple} (hX : X ∈ entryBox) (a : Fin 3 → ℝ) :
    (43 / 100 : ℝ) ^ 2 * euclideanSq a ≤ euclideanSq (applyTriple X a) := by
  let u := applyTriple cyclicCenter a
  let v := applyTriple (X - cyclicCenter) a
  have heq : applyTriple X a = u + v := by
    ext i
    simp only [u, v, applyTriple, Pi.sub_apply, Pi.add_apply, mul_sub, Finset.sum_sub_distrib]
    ring
  have hid : (57 / 100 : ℝ) * euclideanSq (u + v) - (2451 / 10000 : ℝ) * euclideanSq u +
      (43 / 100 : ℝ) * euclideanSq v = euclideanSq ((57 / 100 : ℝ) • u + v) := by
    simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ ↦ by ring
  have hnon := euclideanSq_nonneg ((57 / 100 : ℝ) • u + v)
  have hu : euclideanSq a ≤ euclideanSq u := euclideanSq_center_lower a
  have hv : euclideanSq v ≤ (57 / 100 : ℝ) ^ 2 * euclideanSq a :=
    euclideanSq_perturbation_upper hX a
  rw [heq]
  nlinarith

theorem euclideanSq_column_upper {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    euclideanSq (X j) ≤ 3 * (119 / 100 : ℝ) ^ 2 := by
  have hi (i : Fin 3) : |X j i| ≤ 119 / 100 := by
    have hh := abs_le.mp (hX j i)
    have hc : cyclicCenter j i = -1 ∨ cyclicCenter j i = 1 := by
      simp only [cyclicCenter]; split_ifs <;> simp
    apply abs_le.mpr
    rcases hc with hc | hc <;> rw [hc] at hh <;> constructor <;> linarith
  calc
    _ ≤ ∑ _ : Fin 3, (119 / 100 : ℝ) ^ 2 := Finset.sum_le_sum fun i _ ↦ by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hi i)
    _ = _ := by simp


theorem euclideanSq_add_weighted (u v : Fin 3 → ℝ) :
    euclideanSq (u + v) ≤ 12 * euclideanSq u + (12 / 11) * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (11 * u i - v i)]

theorem euclideanSq_sub_weighted (u v : Fin 3 → ℝ) :
    euclideanSq (u - v) ≤ (13 / 3) * euclideanSq u + (13 / 10) * euclideanSq v := by
  simp only [euclideanSq, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.sub_apply]
  exact Finset.sum_le_sum fun i _ ↦ by nlinarith [sq_nonneg (10 * u i + 3 * v i)]

theorem joint_radial_residual_bound {X : Triple} (hX : X ∈ entryBox) (Z : Triple)
    (a : Fin 3 → ℝ) (b : ℝ) :
    frobeniusSq (Z - b • X) ≤ 110 *
      (frobeniusSq (fun j ↦ Z j - a j • X j) +
        euclideanSq (totalTriple Z - b • totalTriple X)) := by
  let U : Triple := fun j ↦ Z j - a j • X j
  let c : Fin 3 → ℝ := fun j ↦ a j - b
  let D := totalTriple Z - b • totalTriple X
  have he : applyTriple X c = D - totalTriple U := by
    ext i
    simp only [applyTriple, c, D, totalTriple, U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ ↦ by ring
  have hinv := euclideanSq_apply_lower hX c
  rw [he] at hinv
  have hD := euclideanSq_sub_weighted D (totalTriple U)
  have hU := euclideanSq_total_le U
  have hcol (j : Fin 3) : euclideanSq ((Z - b • X) j) ≤
      12 * euclideanSq (U j) + (12 / 11) * ((a j - b) ^ 2 * (3 * (119 / 100 : ℝ) ^ 2)) := by
    have hh : (Z - b • X) j = U j + (a j - b) • X j := by
      ext i
      simp only [U, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
      ring
    rw [hh]
    have h := euclideanSq_add_weighted (U j) ((a j - b) • X j)
    rw [euclideanSq_smul] at h
    have hm := mul_le_mul_of_nonneg_left (euclideanSq_column_upper hX j) (sq_nonneg (a j - b))
    linarith
  have hbound : frobeniusSq (Z - b • X) ≤
      12 * frobeniusSq U + (36 / 11 * (119 / 100 : ℝ) ^ 2) * euclideanSq c := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul] at hh
    change frobeniusSq (Z - b • X) ≤
      12 * frobeniusSq U + (12 / 11) * (euclideanSq c * (3 * (119 / 100 : ℝ) ^ 2)) at hh
    nlinarith
  have hUne := frobeniusSq_nonneg U
  have hDne := euclideanSq_nonneg D
  change frobeniusSq (Z - b • X) ≤ 110 * (frobeniusSq U + euclideanSq D)
  nlinarith

theorem totalTriple_eq (X : Triple) : totalTriple X = X 0 + X 1 + X 2 := by
  simp [totalTriple, Fin.sum_univ_three]

theorem entryBox_column_bounds {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) :
    81 / 100 ≤ |X j i| ∧ |X j i| ≤ 119 / 100 := by
  have h := abs_le.mp (hX j i)
  by_cases hij : i = j
  · simp only [cyclicCenter, if_pos hij] at h
    rw [abs_of_neg (by linarith : X j i < 0)]
    constructor <;> linarith
  · simp only [cyclicCenter, if_neg hij] at h
    rw [abs_of_pos (by linarith : 0 < X j i)]
    constructor <;> linarith

theorem entryBox_total_bounds {X : Triple} (hX : X ∈ entryBox) (i : Fin 3) :
    43 / 100 ≤ totalTriple X i ∧ totalTriple X i ≤ 157 / 100 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  rw [totalTriple_eq]
  simp only [Pi.add_apply]
  fin_cases i <;> norm_num [cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
    constructor <;> linarith!

theorem entryBox_pair_large {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    81 / 50 ≤ |pairTriple X j j| := by
  have h0 := abs_le.mp (hX 0 j)
  have h1 := abs_le.mp (hX 1 j)
  have h2 := abs_le.mp (hX 2 j)
  have hl : 81 / 50 ≤ pairTriple X j j := by
    fin_cases j <;> norm_num [pairTriple, cyclicCenter, Fin.ext_iff] at h0 h1 h2 ⊢ <;>
      linarith!
  exact hl.trans (le_abs_self _)

theorem entryBox_pair_small {X : Triple} (hX : X ∈ entryBox) (j i : Fin 3) (hij : i ≠ j) :
    |pairTriple X j i| ≤ 19 / 50 := by
  have h0 := abs_le.mp (hX 0 i)
  have h1 := abs_le.mp (hX 1 i)
  have h2 := abs_le.mp (hX 2 i)
  fin_cases j <;> fin_cases i <;> first
  | exact (hij rfl).elim
  | norm_num [pairTriple, cyclicCenter, Fin.ext_iff, abs_le] at h0 h1 h2 ⊢
    constructor <;> linarith!

theorem entryBox_column_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) : X j ≠ 0 := by
  intro he
  have h := (entryBox_column_bounds hX j 0).1
  norm_num [he] at h

theorem entryBox_total_ne_zero {X : Triple} (hX : X ∈ entryBox) : totalTriple X ≠ 0 := by
  intro he
  have h := (entryBox_total_bounds hX 0).1
  norm_num [he] at h

theorem entryBox_pair_ne_zero {X : Triple} (hX : X ∈ entryBox) (j : Fin 3) :
    pairTriple X j ≠ 0 := by
  intro he
  have h := entryBox_pair_large hX j
  norm_num [he] at h

theorem euclideanSq_pairs_le (X : Triple) :
    (∑ j, euclideanSq (pairTriple X j)) ≤ 4 * frobeniusSq X := by
  have he : (∑ j, euclideanSq (pairTriple X j)) = frobeniusSq X + euclideanSq (totalTriple X) := by
    rw [totalTriple_eq]
    simp only [pairTriple, frobeniusSq, Fin.sum_univ_three, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    simp only [euclideanSq, Pi.add_apply, Fin.sum_univ_three]
    ring
  rw [he]
  linarith [euclideanSq_total_le X]

theorem lowerHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < lowerHessianCoefficient p := by
  unfold lowerHessianCoefficient
  positivity

theorem upperHessianCoefficient_pos {p : ℝ} (hp : 1 < p) : 0 < upperHessianCoefficient p := by
  unfold upperHessianCoefficient
  positivity

theorem lpNorm_pred_le_three_mul {p M : ℝ} (hp : 1 < p) (hM : 0 ≤ M)
    (v : Fin 3 → ℝ) (hv : ∀ i, |v i| ≤ M) :
    lpNorm p v ^ (p - 1) ≤ 3 * M ^ (p - 1) := by
  have hp0 := zero_lt_one.trans hp
  have hN := lpNorm_le_card_root_mul hp0 hM v hv
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hN
  have hpower := Real.rpow_le_rpow (lpNorm_nonneg p v) hN (by linarith : 0 ≤ p - 1)
  rw [Real.mul_rpow (by positivity) hM, ← Real.rpow_mul (by norm_num)] at hpower
  have he : 1 / p * (p - 1) = 1 - 1 / p := by field_simp
  rw [he] at hpower
  have hthree : (3 : ℝ) ^ (1 - 1 / p) ≤ 3 := by
    have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num)
      (show 1 - 1 / p ≤ 1 by have := one_div_nonneg.mpr hp0.le; linarith)
    simpa only [Real.rpow_one] using h
  exact hpower.trans (mul_le_mul_of_nonneg_right hthree (Real.rpow_nonneg hM _))

theorem normHessian_lower {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ)
    (hlo : ∀ i, 43 / 100 ≤ |v i|) (hhi : ∀ i, |v i| ≤ 157 / 100) :
    lowerHessianCoefficient p * euclideanSq (h - radialCoefficient p v h • v) ≤
      normHessian p v h := by
  have hp0 : 0 < p := by linarith
  have hpred : 0 ≤ p - 1 := by linarith
  have hv : v ≠ 0 := by intro hv; have hh := hlo 0; norm_num [hv] at hh
  have hN := lpNorm_pos hp0 hv
  have hden := lpNorm_pred_le_three_mul (p := p) (by linarith) (by norm_num) v hhi
  have hweight : (43 / 100 : ℝ) ^ (p - 2) *
      euclideanSq (h - radialCoefficient p v h • v) ≤
        powerResidual p v h (radialCoefficient p v h) := by
    simp only [euclideanSq, powerResidual, Finset.mul_sum, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow (by norm_num) (hlo i) (by linarith))
      (sq_nonneg _)
  have hcoefficient : lowerHessianCoefficient p ≤
      ((p - 1) / lpNorm p v ^ (p - 1)) * (43 / 100 : ℝ) ^ (p - 2) := by
    have hh := div_le_div_of_nonneg_left
      (show 0 ≤ (p - 1) * (43 / 100 : ℝ) ^ (p - 2) by positivity)
      (Real.rpow_pos_of_pos hN _) hden
    calc
      _ ≤ ((p - 1) * (43 / 100 : ℝ) ^ (p - 2)) / lpNorm p v ^ (p - 1) := hh
      _ = _ := by ring
  rw [normHessian_eq_div hp0]
  calc
    _ ≤ (((p - 1) / lpNorm p v ^ (p - 1)) * (43 / 100 : ℝ) ^ (p - 2)) *
        euclideanSq (h - radialCoefficient p v h • v) :=
      mul_le_mul_of_nonneg_right hcoefficient (euclideanSq_nonneg _)
    _ = ((p - 1) / lpNorm p v ^ (p - 1)) *
        ((43 / 100 : ℝ) ^ (p - 2) * euclideanSq (h - radialCoefficient p v h • v)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hweight (by positivity)


noncomputable def sharpUpperHessianCoefficient (p : ℝ) : ℝ :=
  (10 / 9) * (p - 1) * (19 / 50 : ℝ) ^ (p - 2) / (81 / 50 : ℝ) ^ (p - 1)

theorem sharpUpperHessianCoefficient_pos {p : ℝ} (hp : 1 < p) :
    0 < sharpUpperHessianCoefficient p := by
  unfold sharpUpperHessianCoefficient
  positivity

theorem erased_residual_sq_le (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) ≤ (10 / 9) * euclideanSq h := by
  have hkv : 0 < |v k| := by linarith
  have hr (i : Fin 3) (hik : i ≠ k) : |v i / v k| ≤ 19 / 81 := by
    rw [abs_div, div_le_iff₀ hkv]
    linarith [hi i hik]
  have hsq (i : Fin 3) (hik : i ≠ k) : (v i / v k) ^ 2 ≤ (19 / 81 : ℝ) ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (by norm_num)).mpr (hr i hik)
  have hterm (i : Fin 3) (hik : i ≠ k) : (h i - h k / v k * v i) ^ 2 ≤
      (10 / 9) * (h i) ^ 2 + 10 * (h k) ^ 2 * (19 / 81 : ℝ) ^ 2 := by
    have hyoung := sq_nonneg (h i / 3 + 3 * h k * (v i / v k))
    have hm := mul_le_mul_of_nonneg_left (hsq i hik) (sq_nonneg (h k))
    have he : h k / v k * v i = h k * (v i / v k) := by ring
    rw [he]
    nlinarith
  have hh := Finset.sum_le_sum (s := Finset.univ.erase k)
    (fun i hi ↦ hterm i (Finset.mem_erase.mp hi).1)
  have hsum : (∑ i ∈ Finset.univ.erase k, (h i) ^ 2) + (h k) ^ 2 = euclideanSq h := by
    exact Finset.sum_erase_add _ _ (Finset.mem_univ k)
  norm_num only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ k), Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hh
  nlinarith [sq_nonneg (h k)]

theorem normHessian_upper {p : ℝ} (hp : 2 < p) (v h : Fin 3 → ℝ) (k : Fin 3)
    (hk : 81 / 50 ≤ |v k|) (hi : ∀ i, i ≠ k → |v i| ≤ 19 / 50) :
    normHessian p v h ≤ sharpUpperHessianCoefficient p * euclideanSq h := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have hkv : v k ≠ 0 := by intro he; norm_num [he] at hk
  have hv : v ≠ 0 := by intro he; apply hkv; simp [he]
  have hN := lpNorm_pos hp0 hv
  have hlarge : 81 / 50 ≤ lpNorm p v := hk.trans (norm_apply_le_lpNorm hp1 v k)
  have hden : (81 / 50 : ℝ) ^ (p - 1) ≤ lpNorm p v ^ (p - 1) :=
    Real.rpow_le_rpow (by norm_num) hlarge (by linarith)
  have hres : powerResidual p v h (h k / v k) ≤
      (19 / 50 : ℝ) ^ (p - 2) * ((10 / 9) * euclideanSq h) := by
    have hz : |v k| ^ (p - 2) * (h k - h k / v k * v k) ^ 2 = 0 := by
      simp [div_mul_cancel₀ _ hkv]
    have he : powerResidual p v h (h k / v k) =
        ∑ i ∈ Finset.univ.erase k, |v i| ^ (p - 2) * (h i - h k / v k * v i) ^ 2 := by
      rw [powerResidual, ← Finset.sum_erase_add _ _ (Finset.mem_univ k), hz, add_zero]
    rw [he]
    calc
      _ ≤ ∑ i ∈ Finset.univ.erase k, (19 / 50 : ℝ) ^ (p - 2) *
          (h i - h k / v k * v i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i hi'
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow (abs_nonneg _) (hi i (Finset.mem_erase.mp hi').1) (by linarith))
          (sq_nonneg _)
      _ = (19 / 50 : ℝ) ^ (p - 2) *
          (∑ i ∈ Finset.univ.erase k, (h i - h k / v k * v i) ^ 2) := (Finset.mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left (erased_residual_sq_le v h k hk hi) (by positivity)
  have hcoef : (p - 1) / lpNorm p v ^ (p - 1) ≤ (p - 1) / (81 / 50 : ℝ) ^ (p - 1) :=
    div_le_div_of_nonneg_left (by linarith) (by positivity) hden
  have hmin := normHessian_le_residual hp v h hv (h k / v k)
  rw [powerSum_root_pred hp0] at hmin
  change normHessian p v h ≤
    (p - 1) / lpNorm p v ^ (p - 1) * powerResidual p v h (h k / v k) at hmin
  calc
    _ ≤ _ := hmin
    _ ≤ ((p - 1) / lpNorm p v ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * ((10 / 9) * euclideanSq h)) :=
      mul_le_mul_of_nonneg_left hres (by positivity)
    _ ≤ ((p - 1) / (81 / 50 : ℝ) ^ (p - 1)) * ((19 / 50 : ℝ) ^ (p - 2) * ((10 / 9) * euclideanSq h)) :=
      mul_le_mul_of_nonneg_right hcoef (mul_nonneg (by positivity)
        (mul_nonneg (by norm_num) (euclideanSq_nonneg h)))
    _ = _ := by unfold sharpUpperHessianCoefficient; ring

theorem hessianCoefficient_ratio (p : ℝ) :
    sharpUpperHessianCoefficient p = lowerHessianCoefficient p * (785 / 243) *
      (2983 / 3483 : ℝ) ^ (p - 2) := by
  have hM : (157 / 100 : ℝ) ^ (p - 1) = (157 / 100 : ℝ) ^ (p - 2) * (157 / 100) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hL : (81 / 50 : ℝ) ^ (p - 1) = (81 / 50 : ℝ) ^ (p - 2) * (81 / 50) := by
    rw [← Real.rpow_add_one (by norm_num)]
    congr 1
    ring
  have hbase : (2983 / 3483 : ℝ) ^ (p - 2) =
      ((19 / 50 : ℝ) ^ (p - 2) * (157 / 100 : ℝ) ^ (p - 2)) /
        ((81 / 50 : ℝ) ^ (p - 2) * (43 / 100 : ℝ) ^ (p - 2)) := by
    rw [show (2983 / 3483 : ℝ) = ((19 / 50) * (157 / 100)) / ((81 / 50) * (43 / 100)) by norm_num,
      Real.div_rpow (by norm_num) (by norm_num), Real.mul_rpow (by norm_num) (by norm_num),
      Real.mul_rpow (by norm_num) (by norm_num)]
  rw [sharpUpperHessianCoefficient, lowerHessianCoefficient, hM, hL, hbase]
  field_simp
  ring

theorem sharpUpperHessianCoefficient_lt {p : ℝ} (hp : 2 < p) :
    sharpUpperHessianCoefficient p < 4 * lowerHessianCoefficient p * (6 / 7 : ℝ) ^ (p - 2) := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hr := Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 6 / 7) (p - 2)
  have hpow := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 2983 / 3483)
    (by norm_num : (2983 / 3483 : ℝ) ≤ 6 / 7) (show 0 ≤ p - 2 by linarith)
  have hm := mul_le_mul_of_nonneg_left hpow
    (show 0 ≤ lowerHessianCoefficient p * (785 / 243) by positivity)
  rw [hessianCoefficient_ratio]
  nlinarith [mul_pos hb hr]

theorem exponential_curvature_margin {p : ℝ} (hp : 87 ≤ p) :
    1760 * p * (6 / 7 : ℝ) ^ (p - 2) < 1 := by
  have hp0 : 0 < p := by linarith
  have hbase : (1760 * 87 : ℝ) < (7 / 6 : ℝ) ^ (85 : ℕ) := by norm_num
  have hlog : (1 / 7 : ℝ) ≤ Real.log (7 / 6) := by
    have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 7 / 6 by norm_num)
    norm_num at h
    exact h
  have hgrowth : p / 87 ≤ (7 / 6 : ℝ) ^ (p - 87) := by
    have h := Real.add_one_le_exp (Real.log (7 / 6) * (p - 87))
    have hm := mul_le_mul_of_nonneg_right hlog (show 0 ≤ p - 87 by linarith)
    rw [Real.rpow_def_of_pos (by norm_num)]
    linarith
  have hr : 0 < (7 / 6 : ℝ) ^ (p - 87) := by positivity
  have hprod := mul_lt_mul_of_pos_right hbase hr
  have he : (7 / 6 : ℝ) ^ (85 : ℕ) * (7 / 6 : ℝ) ^ (p - 87) =
      (7 / 6 : ℝ) ^ (p - 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add (by norm_num)]
    congr 1
    norm_num
    ring
  rw [he] at hprod
  have hlarge : 1760 * p < (7 / 6 : ℝ) ^ (p - 2) := by linarith
  have hinv : (6 / 7 : ℝ) ^ (p - 2) = ((7 / 6 : ℝ) ^ (p - 2))⁻¹ := by
    rw [show (6 / 7 : ℝ) = (7 / 6 : ℝ)⁻¹ by norm_num, Real.inv_rpow (by norm_num)]
  rw [hinv, ← div_eq_mul_inv, div_lt_one (by positivity)]
  exact hlarge

/-- This comparison includes the geometric constant `110` and pair-sum factor `4`. -/
theorem hessian_curvature_margin {p : ℝ} (hp : 87 ≤ p) :
    440 * p * sharpUpperHessianCoefficient p < lowerHessianCoefficient p := by
  have hb := lowerHessianCoefficient_pos (show 1 < p by linarith)
  have hU := sharpUpperHessianCoefficient_lt (show 2 < p by linarith)
  have hsmall := exponential_curvature_margin hp
  have hm := mul_lt_mul_of_pos_left hU (show 0 < 440 * p by linarith)
  have hbsmall := mul_lt_mul_of_pos_left hsmall hb
  nlinarith

theorem pairTriple_sub_smul (X Z : Triple) (a : ℝ) :
    pairTriple (Z - a • X) = pairTriple Z - a • pairTriple X := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

theorem pair_hessian_sum_upper {p : ℝ} (hp : 2 < p) {X : Triple} (hX : X ∈ entryBox)
    (Z : Triple) (a : ℝ) :
    (∑ j, normHessian p (pairTriple X j) (pairTriple Z j)) ≤
      4 * sharpUpperHessianCoefficient p * frobeniusSq (Z - a • X) := by
  have hi (j : Fin 3) : normHessian p (pairTriple X j) (pairTriple Z j) ≤
      sharpUpperHessianCoefficient p * euclideanSq (pairTriple (Z - a • X) j) := by
    rw [pairTriple_sub_smul]
    change normHessian p (pairTriple X j) (pairTriple Z j) ≤
      sharpUpperHessianCoefficient p * euclideanSq (pairTriple Z j - a • pairTriple X j)
    rw [← normHessian_sub_smul hp _ _ (entryBox_pair_ne_zero hX j) a]
    exact normHessian_upper hp _ _ j (entryBox_pair_large hX j) (entryBox_pair_small hX j)
  have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hi j)
  rw [← Finset.mul_sum] at hh
  have hm := mul_le_mul_of_nonneg_left (euclideanSq_pairs_le (Z - a • X))
    (sharpUpperHessianCoefficient_pos (by linarith : 1 < p)).le
  nlinarith

theorem deficitHessian_nonneg {p K : ℝ} (hp : 87 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p)
    {X : Triple} (hX : X ∈ entryBox) (Z : Triple) : 0 ≤ deficitHessian p K X Z := by
  have hp1 : 1 < p := by linarith
  have hp2 : 2 < p := by linarith
  let a : Fin 3 → ℝ := fun j ↦ radialCoefficient p (X j) (Z j)
  let b := radialCoefficient p (totalTriple X) (totalTriple Z)
  let U : Triple := fun j ↦ Z j - a j • X j
  let D := totalTriple Z - b • totalTriple X
  have hcol (j : Fin 3) : lowerHessianCoefficient p * euclideanSq (U j) ≤
      normHessian p (X j) (Z j) := by
    exact normHessian_lower hp2 _ _
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).1])
      (fun i ↦ by linarith [(entryBox_column_bounds hX j i).2])
  have hcols : lowerHessianCoefficient p * frobeniusSq U ≤
      ∑ j, normHessian p (X j) (Z j) := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun j _ ↦ hcol j)
    rwa [← Finset.mul_sum] at hh
  have htotal : lowerHessianCoefficient p * euclideanSq D ≤
      normHessian p (totalTriple X) (totalTriple Z) := by
    apply normHessian_lower hp2
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.1
    · intro i
      have hi := entryBox_total_bounds hX i
      rw [abs_of_pos (by linarith : 0 < totalTriple X i)]
      exact hi.2
  have hcols0 : 0 ≤ ∑ j, normHessian p (X j) (Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hpositive : lowerHessianCoefficient p * (frobeniusSq U + euclideanSq D) ≤
      (2 * K - 1) * (∑ j, normHessian p (X j) (Z j)) +
        normHessian p (totalTriple X) (totalTriple Z) := by
    have hm := mul_nonneg (by linarith : 0 ≤ 2 * K - 2) hcols0
    nlinarith
  have hgeom : frobeniusSq (Z - b • X) ≤ 110 * (frobeniusSq U + euclideanSq D) :=
    joint_radial_residual_bound hX Z a b
  have hpairs := pair_hessian_sum_upper hp2 hX Z b
  have hpair0 : 0 ≤ ∑ j, normHessian p (pairTriple X j) (pairTriple Z j) :=
    Finset.sum_nonneg fun j _ ↦ normHessian_nonneg hp1.le _ _
  have hd := (sharpUpperHessianCoefficient_pos hp1).le
  have hneg1 := mul_le_mul_of_nonneg_left hpairs (show 0 ≤ p by linarith)
  have hneg2 := mul_le_mul_of_nonneg_left hgeom
    (show 0 ≤ 4 * p * sharpUpperHessianCoefficient p by positivity)
  have hneg3 := mul_le_mul_of_nonneg_right hKp hpair0
  have hcurv := mul_le_mul_of_nonneg_right (hessian_curvature_margin hp).le
    (add_nonneg (frobeniusSq_nonneg U) (euclideanSq_nonneg D))
  dsimp only [deficitHessian]
  nlinarith

theorem convex_entryBox : Convex ℝ entryBox := by
  intro X hX Y hY a b ha hb hab j i
  have heq : (a • X + b • Y) j i - cyclicCenter j i =
      a * (X j i - cyclicCenter j i) + b * (Y j i - cyclicCenter j i) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun t : ℝ ↦ t * cyclicCenter j i) hab]
  rw [heq]
  calc
    _ ≤ |a * (X j i - cyclicCenter j i)| + |b * (Y j i - cyclicCenter j i)| := abs_add_le _ _
    _ = a * |X j i - cyclicCenter j i| + b * |Y j i - cyclicCenter j i| := by
      rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    _ ≤ a * (19 / 100) + b * (19 / 100) :=
      add_le_add (mul_le_mul_of_nonneg_left (hX j i) ha)
        (mul_le_mul_of_nonneg_left (hY j i) hb)
    _ = 19 / 100 := by nlinarith


theorem tripleDeficit_eq_sums (p K : ℝ) (X : Triple) :
    tripleDeficit p K X = (2 * K - 1) * (∑ j, lpNorm p (X j)) +
      lpNorm p (totalTriple X) - K * (∑ j, lpNorm p (pairTriple X j)) := by
  simp only [tripleDeficit, hlawkaDeficit, totalTriple_eq, pairTriple, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

theorem totalTriple_add_smul (X Z : Triple) (t : ℝ) :
    totalTriple (X + t • Z) = totalTriple X + t • totalTriple Z := by
  simp [totalTriple, Finset.sum_add_distrib, Finset.smul_sum]

theorem pairTriple_add_smul (X Z : Triple) (t : ℝ) :
    pairTriple (X + t • Z) = pairTriple X + t • pairTriple Z := by
  ext j i
  fin_cases j <;> simp [pairTriple] <;> ring

theorem hasDerivAt_tripleDeficit_line {p : ℝ} (hp : 1 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ tripleDeficit p K (X + s • Z))
      (deficitSlope p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_lpNorm_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_lpNorm_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_lpNorm_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [tripleDeficit_eq_sums, deficitSlope, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

theorem hasDerivAt_deficitSlope_line {p : ℝ} (hp : 4 < p) (K : ℝ) (X Z : Triple) (t : ℝ)
    (ht : X + t • Z ∈ entryBox) :
    HasDerivAt (fun s : ℝ ↦ deficitSlope p K (X + s • Z) Z)
      (deficitHessian p K (X + t • Z) Z) t := by
  have hcol (j : Fin 3) := hasDerivAt_normSlope_line hp (X j) (Z j) t
    (entryBox_column_ne_zero ht j)
  have htotal := hasDerivAt_normSlope_line hp (totalTriple X) (totalTriple Z) t
    (by rw [← totalTriple_add_smul]; exact entryBox_total_ne_zero ht)
  have hpair (j : Fin 3) := hasDerivAt_normSlope_line hp (pairTriple X j) (pairTriple Z j) t
    (by change (pairTriple X + t • pairTriple Z) j ≠ 0
        rw [← pairTriple_add_smul]; exact entryBox_pair_ne_zero ht j)
  have h := (((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hcol j)).const_mul (2 * K - 1)).add
    htotal).sub ((HasDerivAt.fun_sum (u := Finset.univ) (fun j _ ↦ hpair j)).const_mul K)
  convert! h using 1 <;>
    simp only [deficitSlope, deficitHessian, totalTriple_add_smul, pairTriple_add_smul,
      Pi.add_apply, Pi.smul_apply]
  rfl

theorem continuous_tripleDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) :
    Continuous (tripleDeficit p K) := by
  have hc (j : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j)) :=
    (continuous_lpNorm hp).comp (continuous_apply j)
  have ht : Continuous (fun X : Triple ↦ lpNorm p (X 0 + X 1 + X 2)) :=
    (continuous_lpNorm hp).comp
      (((continuous_apply 0).add (continuous_apply 1)).add (continuous_apply 2))
  have hpairs (j k : Fin 3) : Continuous (fun X : Triple ↦ lpNorm p (X j + X k)) :=
    (continuous_lpNorm hp).comp ((continuous_apply j).add (continuous_apply k))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add ht).sub
    (continuous_const.mul (((hpairs 0 1).add (hpairs 0 2)).add (hpairs 1 2)))

theorem _root_.HlawkaSchatten.DiagonalConstruction.cutoff87_convexOn_tripleDeficit {p K : ℝ} (hp : 87 ≤ p) (hK : 1 ≤ K) (hKp : K ≤ p) :
    ConvexOn ℝ entryBox (tripleDeficit p K) := by
  refine ⟨convex_entryBox, ?_⟩
  intro X hX Y hY a b ha hb hab
  let Z := Y - X
  have hline (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : X + t • Z ∈ entryBox := by
    have he : X + t • Z = (1 - t) • X + t • Y := by
      dsimp [Z]
      module
    rw [he]
    exact convex_entryBox hX hY (by linarith [ht.2]) ht.1 (by ring)
  have hcont : Continuous (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) :=
    (continuous_tripleDeficit (by linarith : 0 < p) K).comp
      (continuous_const.add (continuous_id.smul continuous_const))
  have hconv : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (fun t : ℝ ↦ tripleDeficit p K (X + t • Z)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc 0 1) hcont.continuousOn
      (f' := fun t ↦ deficitSlope p K (X + t • Z) Z)
      (f'' := fun t ↦ deficitHessian p K (X + t • Z) Z)
    · intro t ht
      exact (hasDerivAt_tripleDeficit_line (by linarith : 1 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact (hasDerivAt_deficitSlope_line (by linarith : 4 < p) K X Z t
        (hline t (interior_subset ht))).hasDerivWithinAt
    · intro t ht
      exact deficitHessian_nonneg hp hK hKp (hline t (interior_subset ht)) Z
  have h := hconv.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) ha hb hab
  have hpoint : X + b • Z = a • X + b • Y := by
    have haeq : a = 1 - b := by linarith
    rw [haeq]
    dsimp [Z]
    module
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, zero_smul, add_zero, one_smul,
    Z, add_sub_cancel, hpoint] using h


end HlawkaSchatten.DiagonalConstruction.Cutoff87Curvature



open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

namespace HlawkaSchatten.DiagonalCutoff87

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_nonneg (p : ℝ) (x : ι → E) : 0 ≤ lpNorm p x :=
  Real.rpow_nonneg (Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _) _

theorem lpNorm_eq_piLp {p : ℝ} (hp : 0 < p) (x : ι → E) :
    lpNorm p x = ‖WithLp.toLp (ENNReal.ofReal p) x‖ := by
  rw [PiLp.norm_eq_sum (by simpa only [ENNReal.toReal_ofReal hp.le] using hp)]
  simp [lpNorm, ENNReal.toReal_ofReal hp.le]

@[simp]
theorem lpNorm_zero {p : ℝ} (hp : 0 < p) : lpNorm p (0 : ι → E) = 0 := by
  simp [lpNorm, hp.ne']

@[simp]
theorem lpNorm_neg (p : ℝ) (x : ι → E) : lpNorm p (-x) = lpNorm p x := by
  simp [lpNorm]

theorem lpNorm_add {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    lpNorm p (x + y) ≤ lpNorm p x + lpNorm p y := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  simpa only [lpNorm_eq_piLp hp0, ← WithLp.toLp_add] using
    norm_add_le (WithLp.toLp (ENNReal.ofReal p) x) (WithLp.toLp (ENNReal.ofReal p) y)

theorem norm_apply_le_lpNorm {p : ℝ} (hp : 1 ≤ p) (x : ι → E) (i : ι) :
    ‖x i‖ ≤ lpNorm p x := by
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  let : Fact (1 ≤ ENNReal.ofReal p) := ⟨ENNReal.one_le_ofReal.mpr hp⟩
  rw [lpNorm_eq_piLp hp0]
  exact PiLp.norm_apply_le (WithLp.toLp (ENNReal.ofReal p) x) i


/-- The two non-dominant coordinates retain their positive power contribution. -/
theorem norm_le_dominant_with_tail {p : ℝ} (hp : 1 < p)
    (v : Fin 3 → ℝ) (k : Fin 3) (hm : 0 ≤ v k)
    (hsmall : ∀ i, i ≠ k → |v i| ≤ v k / 2) :
    lpNorm p v ≤ v k * (1 + 2 * (1 / 2 : ℝ) ^ p / p) := by
  have hp0 : 0 < p := by linarith
  have hpow (i : Fin 3) (hi : i ≠ k) :
      |v i| ^ p ≤ (v k) ^ p * (1 / 2 : ℝ) ^ p := by
    have h := Real.rpow_le_rpow (abs_nonneg (v i)) (hsmall i hi) hp0.le
    rw [show v k / 2 = v k * (1 / 2) by ring,
      Real.mul_rpow hm (by norm_num)] at h
    exact h
  have hsum : (∑ i, |v i| ^ p) ≤ (v k) ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p) := by
    fin_cases k
    · change 0 ≤ v 0 at hm
      have hleft : |v 1| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      have hright : |v 2| ^ p ≤ v 0 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 0 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 1 at hm
      have hleft : |v 0| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 2| ^ p ≤ v 1 ^ p * (1 / 2 : ℝ) ^ p := hpow 2 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 1 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
    · change 0 ≤ v 2 at hm
      have hleft : |v 0| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 0 (by decide)
      have hright : |v 1| ^ p ≤ v 2 ^ p * (1 / 2 : ℝ) ^ p := hpow 1 (by decide)
      simp only [Fin.sum_univ_three]
      change |v 0| ^ p + |v 1| ^ p + |v 2| ^ p ≤ v 2 ^ p * (1 + 2 * (1 / 2 : ℝ) ^ p)
      rw [abs_of_nonneg hm]
      nlinarith
  have hnorm := Real.rpow_le_rpow
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (abs_nonneg (v i)) p)
    hsum (one_div_nonneg.mpr hp0.le)
  rw [Real.mul_rpow (Real.rpow_nonneg hm _) (by positivity),
    ← Real.rpow_mul hm, mul_one_div_cancel hp0.ne', Real.rpow_one] at hnorm
  have hroot := rpow_one_add_le_one_add_mul_self
    (s := 2 * (1 / 2 : ℝ) ^ p) (p := 1 / p) (by have h := Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 1/2) p; linarith)
    (by positivity) (by simpa using (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hp.le))
  have hmul := mul_le_mul_of_nonneg_left hroot hm
  change lpNorm p v ≤ _ at hnorm
  calc
    _ ≤ v k * (1 + 1 / p * (2 * (1 / 2 : ℝ) ^ p)) := hnorm.trans hmul
    _ = _ := by ring

/-- The strict pair gap absorbs a uniformly bounded, nonzero tail. -/
theorem pair_coordinate_deficit {p : ℝ} (hp : 87 ≤ p)
    (x y : Fin 3 → ℝ) (k : Fin 3)
    (hx : lpNorm p x ≤ 5351 / 15000) (hy : lpNorm p y ≤ 5351 / 15000)
    (hgap : pairGap (lpNorm p) x y < 43 / (30 * p))
    (hm : 0 ≤ x k + y k)
    (hsmall : ∀ i, i ≠ k → |x i + y i| ≤ (x k + y k) / 2) :
    lpNorm p x + lpNorm p y - (x k + y k) < 287 / (200 * p) := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  have ha : (1 / 2 : ℝ) ^ p ≤ 1 / 1024 := by
    calc
      _ ≤ (1 / 2 : ℝ) ^ (10 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
      _ = _ := by norm_num
  have hnorm := norm_le_dominant_with_tail (by linarith : 1 < p) (x + y) k hm hsmall
  have hm' : x k + y k ≤ 5351 / 7500 := by
    have hxk := (le_abs_self (x k)).trans (norm_apply_le_lpNorm hp1 x k)
    have hyk := (le_abs_self (y k)).trans (norm_apply_le_lpNorm hp1 y k)
    linarith
  have ht0 : 0 ≤ 2 * (1 / 2 : ℝ) ^ p / p := by positivity
  have ht : 2 * (1 / 2 : ℝ) ^ p / p ≤ 1 / (512 * p) := by
    apply (mul_le_mul_iff_left₀ hp0).mp
    field_simp
    nlinarith
  have hm1 := mul_le_mul_of_nonneg_left ht hm
  have hm2 := mul_le_mul_of_nonneg_right hm' (show 0 ≤ 1 / (512 * p) by positivity)
  have htail : (5351 / 7500 : ℝ) * (1 / (512 * p)) < 1 / (600 * p) := by
    apply (mul_lt_mul_iff_left₀ hp0).mp
    field_simp
    norm_num
  change lpNorm p (x + y) ≤ (x k + y k) * (1 + 2 * (1 / 2 : ℝ) ^ p / p) at hnorm
  have hE : 43 / (30 * p) + 1 / (600 * p) = 287 / (200 * p) := by field_simp; ring
  dsimp only [pairGap] at hgap
  rw [← hE]
  nlinarith

/-- A coarse cyclic box is sufficient for the refined coordinate estimate. -/
theorem coarse_pair_dominance (X : Triple)
    (hbox : ∀ j i, |3 * X j i - cyclicCenter j i| ≤ (1 / 3 : ℝ))
    (a b k : Fin 3) (hab : a ≠ b) (hak : a ≠ k) (hbk : b ≠ k) :
    0 ≤ X a k + X b k ∧
      ∀ i, i ≠ k → |X a i + X b i| ≤ (X a k + X b k) / 2 := by
  have hak' := abs_le.mp (hbox a k)
  have hbk' := abs_le.mp (hbox b k)
  simp only [cyclicCenter, if_neg (Ne.symm hak), if_neg (Ne.symm hbk)] at hak' hbk'
  refine ⟨by linarith, ?_⟩
  intro i hik
  have ha := abs_le.mp (hbox a i)
  have hb := abs_le.mp (hbox b i)
  have hie : i = a ∨ i = b := by
    fin_cases a <;> fin_cases b <;> fin_cases k <;> fin_cases i <;> simp_all
  rcases hie with rfl | rfl
  · simp only [cyclicCenter, ite_true, if_neg hab] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · simp only [cyclicCenter, ite_true, if_neg (Ne.symm hab)] at ha hb
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The second localization stage keeps the orientation fixed. -/
theorem cutoff87_bootstrap {p : ℝ} (hp : 87 ≤ p) (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ 5351 / 15000)
    (hy : lpNorm p y ≤ 5351 / 15000)
    (hz : lpNorm p z ≤ 5351 / 15000)
    (hT : lpNorm p (x + y + z) ≤ 5351 / 15000)
    (hgap : pairGapSum (lpNorm p) x y z < 43 / (30 * p))
    (hbox : ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ)) :
    ![(3 : ℝ) • x, (3 : ℝ) • y, (3 : ℝ) • z] ∈ entryBox := by
  have hp1 : 1 ≤ p := by linarith
  have hxy0 : 0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp1 x y)
  have hxz0 : 0 ≤ pairGap (lpNorm p) x z := sub_nonneg.mpr (lpNorm_add hp1 x z)
  have hyz0 : 0 ≤ pairGap (lpNorm p) y z := sub_nonneg.mpr (lpNorm_add hp1 y z)
  have hxy := coarse_pair_dominance ![x,y,z] hbox 0 1 2 (by decide) (by decide) (by decide)
  have hxz := coarse_pair_dominance ![x,y,z] hbox 0 2 1 (by decide) (by decide) (by decide)
  have hyz := coarse_pair_dominance ![x,y,z] hbox 1 2 0 (by decide) (by decide) (by decide)
  dsimp only [pairGapSum] at hgap
  have hxyE := pair_coordinate_deficit hp x y 2 hx hy (by linarith) hxy.1 hxy.2
  have hxzE := pair_coordinate_deficit hp x z 1 hx hz (by linarith) hxz.1 hxz.2
  have hyzE := pair_coordinate_deficit hp y z 0 hy hz (by linarith) hyz.1 hyz.2
  have hE : 287 / (200 * p) ≤ (287 / 17400 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i ≤ 5351 / 15000 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : lpNorm p (c • x) = |c| * lpNorm p x := by
  unfold lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

theorem pairGap_nonneg {p : ℝ} (hp : 1 ≤ p) (x y : ι → E) :
    0 ≤ pairGap (lpNorm p) x y := sub_nonneg.mpr (lpNorm_add hp x y)

theorem pairGapSum_nonneg {p : ℝ} (hp : 1 ≤ p) (x y z : ι → E) :
    0 ≤ pairGapSum (lpNorm p) x y z :=
  add_nonneg (add_nonneg (pairGap_nonneg hp x y) (pairGap_nonneg hp x z))
    (pairGap_nonneg hp y z)

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (lpNorm p) x y z - tripleGap (lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_swap_left (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K y x z = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_swap_right (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x z y = hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, add_comm, add_left_comm, add_assoc]

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

theorem scalarEnvelopeRoot_lt_one {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    scalarEnvelopeRoot p q < 1 := by
  have hpow : q ^ p < 1 := by
    simpa only [Real.one_rpow] using Real.rpow_lt_rpow hq hq1 hp
  have hbase : 0 ≤ (1 + q ^ p) / 2 := by positivity
  have hroot := Real.rpow_lt_rpow hbase (show (1 + q ^ p) / 2 < 1 by linarith)
    (one_div_pos.mpr hp)
  simpa only [Real.one_rpow, scalarEnvelopeRoot] using hroot

theorem scalarEnvelope_denominator_pos {p q : ℝ} (hp : 0 < p) (hq : 0 ≤ q) (hq1 : q < 1) :
    0 < 2 * (1 - scalarEnvelopeRoot p q) := by
  have h := scalarEnvelopeRoot_lt_one hp hq hq1
  linarith

theorem failure_ne_zero {p K : ℝ} (hp : 1 ≤ p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hf : hlawkaDeficit p K x y z < 0) :
    x ≠ 0 ∧ y ≠ 0 ∧ z ≠ 0 := by
  have hfirst (u v w : ι → ℝ) (h : hlawkaDeficit p K u v w < 0) : u ≠ 0 := by
    intro hu
    subst u
    simp only [hlawkaDeficit, lpNorm_zero (zero_lt_one.trans_le hp), zero_add] at h
    have ht := lpNorm_add hp v w
    have hm := mul_nonneg (sub_nonneg.mpr hK)
      (show 0 ≤ lpNorm p v + lpNorm p w - lpNorm p (v + w) by linarith)
    nlinarith
  refine ⟨hfirst x y z hf, hfirst y x z ?_, hfirst z x y ?_⟩
  · rwa [hlawkaDeficit_swap_left]
  · rwa [hlawkaDeficit_swap_left, hlawkaDeficit_swap_right]

theorem normalized_failure_total_lt_one {p K : ℝ} (hp : 1 ≤ p) (hK : 0 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) : lpNorm p (x + y + z) < 1 := by
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf
  have hprod := mul_nonneg hK (pairGapSum_nonneg hp x y z)
  linarith

theorem normalized_failure_ratio_lt_envelope {p K : ℝ} (hp : 1 < p) (hK : 1 ≤ K)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p K x y z < 0) :
    K < scalarEnvelope p (lpNorm p (x + y + z)) := by
  have hp0 := zero_lt_one.trans hp
  have hn := failure_ne_zero hp.le hK x y z hf
  have hq0 := lpNorm_nonneg p (x + y + z)
  have hq1 := normalized_failure_total_lt_one hp.le (by linarith) x y z hS hf
  have hP := normalized_pair_sum_le hp x y z hn.1 hn.2.1 hn.2.2 hS
  have hden := scalarEnvelope_denominator_pos hp0 hq0 hq1
  have hgap : 2 * (1 - scalarEnvelopeRoot p (lpNorm p (x + y + z))) ≤
      pairGapSum (lpNorm p) x y z := by
    dsimp only [pairGapSum, pairGap]
    linarith
  have hgap0 : 0 < pairGapSum (lpNorm p) x y z := hden.trans_le hgap
  have hR : K < (1 - lpNorm p (x + y + z)) / pairGapSum (lpNorm p) x y z := by
    rw [lt_div_iff₀ hgap0]
    rw [hlawkaDeficit_eq, tripleGap, hS] at hf
    linarith
  exact hR.trans_le (div_le_div_of_nonneg_left (by linarith) hden hgap)

theorem normalized_failure_total_lt_q0 {p : ℝ} (hp : 87 ≤ p)
    (hlinear : (20 / 43 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (5351 / 15000) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    lpNorm p (x + y + z) < 5351 / 15000 := by
  have hp1 : 1 < p := by linarith
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hq1 := normalized_failure_total_lt_one hp1.le (by linarith) x y z hS hf
  have henv := normalized_failure_ratio_lt_envelope hp1 hK x y z hS hf
  by_contra hn
  have hq0 : (5351 / 15000 : ℝ) ≤ lpNorm p (x + y + z) := le_of_not_gt hn
  have hm := antitoneOn_scalarEnvelope hp1.le
    (show (5351 / 15000 : ℝ) ∈ Set.Ico 0 1 by norm_num)
    (show lpNorm p (x + y + z) ∈ Set.Ico 0 1 from ⟨lpNorm_nonneg p _, hq1⟩) hq0
  linarith [henvelope]

/-- The scalar data used by the coordinate argument. -/
theorem normalized_failure_confinement {p : ℝ} (hp : 87 ≤ p)
    (hlinear : (20 / 43 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (5351 / 15000) < cyclicConstant p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 5351 / 15000) ∧
      pairGapSum (lpNorm p) x y z < 43 / (30 * p) ∧
      (2149 / 7500 < lpNorm p x ∧ lpNorm p x < 5351 / 15000) ∧
      (2149 / 7500 < lpNorm p y ∧ lpNorm p y < 5351 / 15000) ∧
      (2149 / 7500 < lpNorm p z ∧ lpNorm p z < 5351 / 15000) := by
  have hp1 : 1 < p := by linarith
  have hq := normalized_failure_total_lt_q0 hp hlinear henvelope x y z hS hf
  have hqLower : 1 / 3 ≤ lpNorm p (x + y + z) := by linarith
  have hD := pairGapSum_nonneg hp1.le x y z
  have hK := hlinear
  have hmul := mul_le_mul_of_nonneg_right hK.le hD
  have hf' := hf
  rw [hlawkaDeficit_eq, tripleGap, hS] at hf'
  have hsmall : pairGapSum (lpNorm p) x y z < 43 / (30 * p) := by
    rw [lt_div_iff₀ (show 0 < 30 * p by linarith)]
    nlinarith
  exact ⟨⟨hqLower, hq⟩, hsmall, ⟨by linarith, hx.trans_lt hq⟩,
    ⟨by linarith, hy.trans_lt hq⟩, ⟨by linarith, hz.trans_lt hq⟩⟩

theorem lpNorm_le_three_root_mul_max {p : ℝ} (hp : 0 < p) (x : Fin 3 → ℝ)
    (i : Fin 3) (hi : ∀ j, |x j| ≤ |x i|) :
    lpNorm p x ≤ (3 : ℝ) ^ (1 / p) * |x i| := by
  have hsum : (∑ j, |x j| ^ p) ≤ 3 * |x i| ^ p := by
    calc
      _ ≤ ∑ _ : Fin 3, |x i| ^ p :=
        Finset.sum_le_sum fun j _ ↦ Real.rpow_le_rpow (abs_nonneg _) (hi j) hp.le
      _ = _ := by simp
  have h := Real.rpow_le_rpow
    (Finset.sum_nonneg fun j _ ↦ Real.rpow_nonneg (abs_nonneg (x j)) p)
    hsum (one_div_nonneg.mpr hp.le)
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg (abs_nonneg _) _),
    ← Real.rpow_mul (abs_nonneg (x i)), mul_one_div_cancel hp.ne', Real.rpow_one] at h
  simpa only [lpNorm, Real.norm_eq_abs] using h

theorem inverse_three_root_deficit (p : ℝ) :
    1 - ((3 : ℝ) ^ (1 / p))⁻¹ ≤ Real.log 3 / p := by
  have h := Real.add_one_le_exp (-(Real.log 3 / p))
  have he : ((3 : ℝ) ^ (1 / p))⁻¹ = Real.exp (-(Real.log 3 / p)) := by
    rw [Real.rpow_def_of_pos (by norm_num), ← Real.exp_neg]
    congr 1
    ring
  rw [he]
  linarith

theorem signed_entry_le_norm {p s : ℝ} (hp : 1 ≤ p) (hs : |s| = 1)
    (x : Fin 3 → ℝ) (i : Fin 3) : s * x i ≤ lpNorm p x := by
  calc
    _ ≤ |s * x i| := le_abs_self _
    _ = |x i| := by rw [abs_mul, hs, one_mul]
    _ ≤ _ := norm_apply_le_lpNorm hp x i

/-- Small pair gap forces two large entries with one common sign. -/
theorem exists_large_signed_pair {p : ℝ} (hp : 87 ≤ p) (x y : Fin 3 → ℝ)
    (hx : lpNorm p x < 5351 / 15000) (hy : lpNorm p y < 5351 / 15000)
    (hgap : pairGap (lpNorm p) x y < 43 / (30 * p)) :
    ∃ i : Fin 3, ∃ s : ℝ, (s = 1 ∨ s = -1) ∧
      lpNorm p x - 9 / (4 * p) < s * x i ∧
      lpNorm p y - 9 / (4 * p) < s * y i := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 ≤ p := by linarith
  obtain ⟨i, _, hi⟩ := Finset.univ.exists_max_image (fun i ↦ |(x + y) i|)
    Finset.univ_nonempty
  have hmax := lpNorm_le_three_root_mul_max hp0 (x + y) i (fun j ↦ hi j (Finset.mem_univ _))
  let c := ((3 : ℝ) ^ (1 / p))⁻¹
  have hc0 : 0 < c := by dsimp [c]; positivity
  have hc1 : c ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact Real.one_le_rpow (by norm_num) (by positivity)
  have hmax' : c * lpNorm p (x + y) ≤ |x i + y i| := by
    have hm := mul_le_mul_of_nonneg_left hmax hc0.le
    have he : c * ((3 : ℝ) ^ (1 / p) * |(x + y) i|) = |(x + y) i| := by
      dsimp [c]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
    rw [he] at hm
    exact hm
  have hd : 1 - c ≤ Real.log 3 / p := inverse_three_root_deficit p
  have hlog3 : Real.log 3 < 11 / 10 := by linarith [Real.log_three_lt_d9]
  have hs0 : 0 ≤ lpNorm p x + lpNorm p y := add_nonneg (lpNorm_nonneg p x) (lpNorm_nonneg p y)
  have hbound : lpNorm p x + lpNorm p y - |x i + y i| < 9 / (4 * p) := by
    have hS : lpNorm p x + lpNorm p y < 5351 / 7500 := by linarith
    have hdef := mul_le_mul_of_nonneg_right hd hs0
    have hg := pairGap_nonneg hp1 x y
    have hgap' := mul_le_mul_of_nonneg_right hc1 hg
    have hlogP : 0 ≤ Real.log 3 / p := by positivity
    have hSlog := mul_le_mul_of_nonneg_left hS.le hlogP
    have hlogDiv := (div_lt_div_iff_of_pos_right hp0).mpr hlog3
    have hlogLast := mul_lt_mul_of_pos_right hlogDiv (by norm_num : (0 : ℝ) < 5351 / 7500)
    dsimp only [pairGap] at hgap hg hgap'
    have hnum : Real.log 3 / p * (5351 / 7500 : ℝ) + 43 / (30 * p) < 9 / (4 * p) := by
      have hrat : (11 / 10 : ℝ) / p * (5351 / 7500) + 43 / (30 * p) < 9 / (4 * p) := by
        apply (mul_lt_mul_iff_left₀ hp0).mp
        field_simp
        norm_num
      linarith
    nlinarith
  by_cases hi0 : 0 ≤ x i + y i
  · rw [abs_of_nonneg hi0] at hbound
    have hxi := signed_entry_le_norm hp1 (s := 1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := 1) (by norm_num) y i
    exact ⟨i, 1, Or.inl rfl, by linarith, by linarith⟩
  · rw [abs_of_neg (lt_of_not_ge hi0)] at hbound
    have hxi := signed_entry_le_norm hp1 (s := -1) (by norm_num) x i
    have hyi := signed_entry_le_norm hp1 (s := -1) (by norm_num) y i
    exact ⟨i, -1, Or.inr rfl, by linarith, by linarith⟩

theorem orient_add (e : Equiv.Perm (Fin 3)) (s x y : Fin 3 → ℝ) :
    orient e s (x + y) = orient e s x + orient e s y := by
  ext i
  exact mul_add _ _ _

theorem lpNorm_orient (p : ℝ) (e : Equiv.Perm (Fin 3)) (s x : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) : lpNorm p (orient e s x) = lpNorm p x := by
  calc
    _ = lpNorm p (x ∘ e) := by simp [lpNorm, orient, hs, Real.norm_eq_abs]
    _ = _ := lpNorm_comp_equiv p x e

theorem hlawkaDeficit_orient (p K : ℝ) (e : Equiv.Perm (Fin 3)) (s x y z : Fin 3 → ℝ)
    (hs : ∀ i, |s i| = 1) :
    hlawkaDeficit p K (orient e s x) (orient e s y) (orient e s z) =
      hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← orient_add, lpNorm_orient p e s _ hs]

private theorem signed_row_conflict {a b c A B C q E s r : ℝ}
    (hs : s = 1 ∨ s = -1) (hr : r = 1 ∨ r = -1)
    (ha : E < A) (hsum : q < A + B + C - 3 * E)
    (hsa : A - E < s * a) (hsb : B - E < s * b)
    (hra : A - E < r * a) (hrc : C - E < r * c)
    (habs : |a + b + c| ≤ q) : False := by
  have heq : r = s := by
    rcases hs with rfl | rfl <;> rcases hr with rfl | rfl <;> first | rfl | exfalso; linarith
  subst r
  have hsabs : |s| = 1 := by rcases hs with rfl | rfl <;> norm_num
  have hu : s * (a + b + c) ≤ q := by
    calc
      _ ≤ |s * (a + b + c)| := le_abs_self _
      _ = |a + b + c| := by rw [abs_mul, hsabs, one_mul]
      _ ≤ q := habs
  nlinarith

private theorem oriented_triple_in_coarse_box {p : ℝ} (hp : 87 ≤ p)
    (x y z : Fin 3 → ℝ)
    (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : 2149 / 7500 < lpNorm p x ∧ lpNorm p x < 5351 / 15000)
    (hy : 2149 / 7500 < lpNorm p y ∧ lpNorm p y < 5351 / 15000)
    (hz : 2149 / 7500 < lpNorm p z ∧ lpNorm p z < 5351 / 15000)
    (hT : lpNorm p (x + y + z) < 5351 / 15000)
    (hx1 : lpNorm p x - 9 / (4 * p) < x 1)
    (hx2 : lpNorm p x - 9 / (4 * p) < x 2)
    (hy0 : lpNorm p y - 9 / (4 * p) < y 0)
    (hy2 : lpNorm p y - 9 / (4 * p) < y 2)
    (hz0 : lpNorm p z - 9 / (4 * p) < z 0)
    (hz1 : lpNorm p z - 9 / (4 * p) < z 1) :
    ∀ j i, |3 * (![x,y,z] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
  have hp1 : 1 ≤ p := by linarith
  have hE : 9 / (4 * p) ≤ (9 / 348 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hxi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 x i)
  have hyi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 y i)
  have hzi (i : Fin 3) := abs_le.mp (norm_apply_le_lpNorm hp1 z i)
  have ht (i : Fin 3) : x i + y i + z i < 5351 / 15000 :=
    ((le_abs_self (x i + y i + z i)).trans
      (norm_apply_le_lpNorm hp1 (x + y + z) i)).trans_lt hT
  intro j i
  fin_cases j <;> fin_cases i <;>
    norm_num [cyclicCenter, Pi.smul_apply, smul_eq_mul, abs_le] <;>
    constructor <;> linarith! [hxi 0, hxi 1, hxi 2, hyi 0, hyi 1, hyi 2,
      hzi 0, hzi 1, hzi 2, ht 0, ht 1, ht 2]


theorem cutoff87_exists_failure_in_entryBox {p : ℝ} (hp : 87 ≤ p)
    (hlinear : (20 / 43 : ℝ) * p < cyclicConstant p)
    (henvelope : scalarEnvelope p (5351 / 15000) < cyclicConstant p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ entryBox, tripleDeficit p (cyclicConstant p) X < 0 := by
  have hp0 : 0 < p := by linarith
  have hp1 : 1 < p := by linarith
  obtain ⟨x, y, z, hf, hS, hxT, hyT, hzT⟩ :=
    exists_normalized_failure hp0 (by linarith : 1 ≤ cyclicConstant p) x y z hf
  obtain ⟨⟨_, hT⟩, hgap, hx, hy, hz⟩ :=
    normalized_failure_confinement hp hlinear henvelope x y z hS hxT hyT hzT hf
  have hxy0 := pairGap_nonneg hp1.le x y
  have hxz0 := pairGap_nonneg hp1.le x z
  have hyz0 := pairGap_nonneg hp1.le y z
  have hgapTotal := hgap
  dsimp only [pairGapSum] at hgap
  obtain ⟨i, s, hs, hsx, hsy⟩ := exists_large_signed_pair hp x y hx.2 hy.2 (by linarith)
  obtain ⟨j, r, hr, hrx, hrz⟩ := exists_large_signed_pair hp x z hx.2 hz.2 (by linarith)
  obtain ⟨k, t, ht, hty, htz⟩ := exists_large_signed_pair hp y z hy.2 hz.2 (by linarith)
  have hE : 9 / (4 * p) ≤ (9 / 348 : ℝ) := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have habs (l : Fin 3) : |x l + y l + z l| ≤ lpNorm p (x + y + z) :=
    norm_apply_le_lpNorm hp1.le (x + y + z) l
  have hij : i ≠ j := by
    intro heq
    subst j
    exact signed_row_conflict hs hr (by linarith [hx.1]) (by linarith)
      hsx hsy hrx hrz (habs i)
  have hik : i ≠ k := by
    intro heq
    subst k
    have hsym : |y i + x i + z i| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs i
    exact signed_row_conflict hs ht (by linarith [hy.1]) (by linarith)
      hsy hsx hty htz hsym
  have hjk : j ≠ k := by
    intro heq
    subst k
    have hsym : |z j + x j + y j| ≤ lpNorm p (x + y + z) := by
      simpa only [add_comm, add_left_comm, add_assoc] using habs j
    exact signed_row_conflict hr ht (by linarith [hz.1]) (by linarith)
      hrz hrx htz hty hsym
  let f : Fin 3 → Fin 3 := ![k, j, i]
  have hfInj : Function.Injective f := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f, Ne.symm hij, Ne.symm hik, Ne.symm hjk]
  let e : Equiv.Perm (Fin 3) := Equiv.ofBijective f hfInj.bijective_of_finite
  let signs : Fin 3 → ℝ := ![t, r, s]
  have hsigns : ∀ l, |signs l| = 1 := by
    intro l
    fin_cases l
    · rcases ht with rfl | rfl <;> norm_num [signs]
    · rcases hr with rfl | rfl <;> norm_num [signs]
    · rcases hs with rfl | rfl <;> norm_num [signs]
  let u := orient e signs x
  let v := orient e signs y
  let w := orient e signs z
  have hu : lpNorm p u = lpNorm p x := lpNorm_orient p e signs x hsigns
  have hv : lpNorm p v = lpNorm p y := lpNorm_orient p e signs y hsigns
  have hw : lpNorm p w = lpNorm p z := lpNorm_orient p e signs z hsigns
  have hsumNorm : lpNorm p (u + v + w) = lpNorm p (x + y + z) := by
    dsimp [u, v, w]
    rw [← orient_add, ← orient_add, lpNorm_orient p e signs _ hsigns]
  have hcoarse : ∀ j i, |3 * (![u,v,w] : Triple) j i - cyclicCenter j i| ≤ (1 / 3 : ℝ) := by
    apply oriented_triple_in_coarse_box hp u v w
    · rwa [hu, hv, hw]
    · rwa [hu]
    · rwa [hv]
    · rwa [hw]
    · rwa [hsumNorm]
    · simpa [hu, u, orient, e, f, signs] using hrx
    · simpa [hu, u, orient, e, f, signs] using hsx
    · simpa [hv, v, orient, e, f, signs] using hty
    · simpa [hv, v, orient, e, f, signs] using hsy
    · simpa [hw, w, orient, e, f, signs] using htz
    · simpa [hw, w, orient, e, f, signs] using hrz
  have hgapOriented : pairGapSum (lpNorm p) u v w < 43 / (30 * p) := by
    dsimp [u,v,w]
    simpa only [pairGapSum, pairGap, ← orient_add, lpNorm_orient p e signs _ hsigns] using hgapTotal
  refine ⟨![(3 : ℝ) • u, (3 : ℝ) • v, (3 : ℝ) • w], ?_, ?_⟩
  · apply cutoff87_bootstrap hp u v w
    · rwa [hu,hv,hw]
    · rw [hu]; exact hx.2.le
    · rw [hv]; exact hy.2.le
    · rw [hw]; exact hz.2.le
    · rw [hsumNorm]; exact hT.le
    · exact hgapOriented
    · exact hcoarse
  · change hlawkaDeficit p (cyclicConstant p) ((3 : ℝ) • u) ((3 : ℝ) • v) ((3 : ℝ) • w) < 0
    rw [hlawkaDeficit_smul hp0]
    have hfail : hlawkaDeficit p (cyclicConstant p) u v w < 0 := by
      dsimp [u, v, w]
      rwa [hlawkaDeficit_orient p (cyclicConstant p) e signs x y z hsigns]
    norm_num only [abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    linarith

end HlawkaSchatten.DiagonalCutoff87

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa

Adapted from the published diagonal construction to isolate the transfer
from a real three-coordinate bound, without any stronger cutoff hypothesis.
-/

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction MeasureTheory

namespace Cutoff87Integration

section NormLaws
variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]

theorem lpNorm_const {p : ℝ} (hp : 0 < p) (x : E) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (fun _ : ι ↦ x) = (Fintype.card ι : ℝ) ^ (1 / p) * ‖x‖ := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Real.mul_rpow (Nat.cast_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _),
    ← Real.rpow_mul (norm_nonneg x), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_smul [NormedSpace ℝ E] {p : ℝ} (hp : 0 < p)
    (c : ℝ) (x : ι → E) : _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (c • x) = |c| * _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p x := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs,
    Real.mul_rpow (abs_nonneg c) (norm_nonneg _), ← Finset.mul_sum]
  rw [Real.mul_rpow (Real.rpow_nonneg (abs_nonneg c) _)
    (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg (x i)) _),
    ← Real.rpow_mul (abs_nonneg c), mul_one_div_cancel hp.ne', Real.rpow_one]

theorem lpNorm_comp_equiv {κ : Type*} [Fintype κ]
    (p : ℝ) (x : κ → E) (e : ι ≃ κ) : lpNorm p (x ∘ e) = lpNorm p x := by
  unfold HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  exact e.sum_comp (fun i ↦ ‖x i‖ ^ p)

end NormLaws

theorem cyclicA_pos {p t : ℝ} (ht : 0 ≤ t) : 0 < cyclicA p t := by
  unfold cyclicA
  exact Real.rpow_pos_of_pos (by positivity) _

theorem continuous_cyclicA {p : ℝ} (hp : 0 < p) : Continuous (cyclicA p) := by
  exact ((Real.continuous_rpow_const hp.le).add continuous_const).rpow_const
    (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))

theorem continuous_cyclicB {p : ℝ} (hp : 0 < p) : Continuous (cyclicB p) := by
  apply Continuous.rpow_const _ (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact (continuous_const.mul
    ((continuous_const.sub continuous_id).abs.rpow_const
      (fun _ ↦ Or.inr hp.le))).add continuous_const

theorem continuousOn_cyclicRatio {p : ℝ} (hp : 1 < p) :
    ContinuousOn (cyclicRatio p) (Set.Ici 0) := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  apply ContinuousOn.div
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_const.sub continuous_id).abs)).continuousOn
  · exact ((continuous_const.mul (continuous_cyclicA hp0)).sub
      (continuous_const.mul (continuous_cyclicB hp0))).continuousOn
  · intro t ht
    exact (cyclic_denominator_pos hp ht).ne'

theorem cyclicRatio_le_constant {p t : ℝ} (hp : 1 < p)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) 2) : cyclicRatio p t ≤ cyclicConstant p := by
  have hc := (continuousOn_cyclicRatio hp).mono
    (show Set.Icc (1 / 2 : ℝ) 2 ⊆ Set.Ici 0 from fun s hs ↦ by
      simp only [Set.mem_Ici]; linarith [hs.1])
  exact le_csSup (isCompact_Icc.image_of_continuousOn hc).bddAbove
    (Set.mem_image_of_mem (cyclicRatio p) ht)

theorem cyclicRatio_two (p : ℝ) : cyclicRatio p 2 = 1 := by
  have hA : 0 < cyclicA p 2 := cyclicA_pos (by norm_num)
  have hB : cyclicB p 2 = cyclicA p 2 := by
    norm_num [cyclicA, cyclicB, add_comm]
  rw [cyclicRatio, hB]
  norm_num only [sub_self, abs_zero, mul_zero, sub_zero]
  have hden : 6 * cyclicA p 2 - 3 * cyclicA p 2 = 3 * cyclicA p 2 := by ring
  rw [hden, div_self (by positivity)]

theorem one_le_cyclicConstant {p : ℝ} (hp : 1 < p) : 1 ≤ cyclicConstant p := by
  rw [← cyclicRatio_two p]
  exact cyclicRatio_le_constant hp (by norm_num)

theorem lpNorm_cyclicX {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicX, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicY {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicY, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicZ {p t : ℝ} (ht : 0 ≤ t) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicZ t) = cyclicA p t := by
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicZ, cyclicA, Fin.sum_univ_three, abs_of_nonneg ht]
  congr 1
  ring

theorem lpNorm_cyclicXY (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t) = cyclicB p t := by
  have he : cyclicX t + cyclicY t = ![1 - t, 1 - t, 2] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicXZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicZ t) = cyclicB p t := by
  have he : cyclicX t + cyclicZ t = ![1 - t, 2, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicYZ (p t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicY t + cyclicZ t) = cyclicB p t := by
  have he : cyclicY t + cyclicZ t = ![2, 1 - t, 1 - t] := by
    ext i
    fin_cases i <;> simp [cyclicY, cyclicZ] <;> ring
  rw [he]
  simp [_root_.HlawkaSchatten.DiagonalConstruction.lpNorm, cyclicB, Fin.sum_univ_three]
  congr 1
  ring

theorem lpNorm_cyclicXYZ {p : ℝ} (hp : 0 < p) (t : ℝ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (cyclicX t + cyclicY t + cyclicZ t) =
      (3 : ℝ) ^ (1 / p) * |2 - t| := by
  have he : cyclicX t + cyclicY t + cyclicZ t = fun _ ↦ 2 - t := by
    ext i
    fin_cases i <;> simp [cyclicX, cyclicY, cyclicZ] <;> ring
  rw [he, lpNorm_const hp]
  simp

theorem cyclic_tripleGap {p t : ℝ} (hp : 0 < p) (ht : 0 ≤ t) :
    tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      3 * cyclicA p t - (3 : ℝ) ^ (1 / p) * |2 - t| := by
  rw [tripleGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht, lpNorm_cyclicZ ht,
    lpNorm_cyclicXYZ hp]
  ring

theorem cyclic_pairGapSum {p t : ℝ} (ht : 0 ≤ t) :
    pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) (cyclicX t) (cyclicY t) (cyclicZ t) =
      6 * cyclicA p t - 3 * cyclicB p t := by
  simp only [pairGapSum, pairGap, lpNorm_cyclicX ht, lpNorm_cyclicY ht,
    lpNorm_cyclicZ ht, lpNorm_cyclicXY, lpNorm_cyclicXZ, lpNorm_cyclicYZ]
  ring

section Deficit
variable {ι : Type*} [Fintype ι]

theorem hlawkaDeficit_eq (p K : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K x y z =
      K * pairGapSum (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z - tripleGap (_root_.HlawkaSchatten.DiagonalConstruction.lpNorm p) x y z := by
  unfold hlawkaDeficit pairGapSum pairGap tripleGap
  ring

theorem hlawkaDeficit_smul {p : ℝ} (hp : 0 < p) (K c : ℝ) (x y z : ι → ℝ) :
    hlawkaDeficit p K (c • x) (c • y) (c • z) = |c| * hlawkaDeficit p K x y z := by
  simp only [hlawkaDeficit, ← smul_add, lpNorm_smul hp]
  ring

end Deficit

theorem conjugate_mem_entryBox (e : Equiv.Perm (Fin 3)) {X : Triple} (hX : X ∈ entryBox) :
    conjugate e X ∈ entryBox := by
  intro j i
  simpa [conjugate, cyclicCenter, e.injective.eq_iff] using hX (e j) (e i)

private def permutations : Fin 6 → Equiv.Perm (Fin 3) :=
  ![Equiv.refl _, Equiv.swap 0 1, Equiv.swap 0 2, Equiv.swap 1 2,
    (Equiv.swap 0 1).trans (Equiv.swap 1 2), (Equiv.swap 1 2).trans (Equiv.swap 0 1)]

private theorem tripleDeficit_conjugate_six (p K : ℝ) (X : Triple) (k : Fin 6) :
    tripleDeficit p K (conjugate (permutations k) X) = tripleDeficit p K X := by
  have he (e : Equiv.Perm (Fin 3)) :
      tripleDeficit p K (conjugate e X) = hlawkaDeficit p K (X (e 0)) (X (e 1)) (X (e 2)) := by
    have hsum (u v : Fin 3 → ℝ) : u ∘ e + v ∘ e = (u + v) ∘ e := rfl
    change hlawkaDeficit p K (X (e 0) ∘ e) (X (e 1) ∘ e) (X (e 2) ∘ e) = _
    simp only [hlawkaDeficit, hsum, lpNorm_comp_equiv]
  rw [he]
  fin_cases k <;> simp [permutations, tripleDeficit, hlawkaDeficit, Equiv.swap_apply_def,
    add_comm, add_left_comm, add_assoc]

theorem orbitAverage_apply (X : Triple) (j i : Fin 3) :
    orbitAverage X j i = if i = j then averageDiagonal X else averageOffDiagonal X := by
  fin_cases j <;> fin_cases i <;>
    norm_num [orbitAverage, permutations, conjugate, Fin.sum_univ_succ, Equiv.swap_apply_def,
      averageDiagonal, averageOffDiagonal, Fin.ext_iff] <;> ring!

theorem orbitAverage_mem_entryBox {X : Triple} (hX : X ∈ entryBox) : orbitAverage X ∈ entryBox := by
  apply convex_entryBox.sum_mem (t := Finset.univ)
  · intros; norm_num
  · norm_num
  · intro k _
    exact conjugate_mem_entryBox _ hX

theorem tripleDeficit_orbitAverage_le {p K : ℝ}
    (hc : ConvexOn ℝ entryBox (tripleDeficit p K)) {X : Triple} (hX : X ∈ entryBox) :
    tripleDeficit p K (orbitAverage X) ≤ tripleDeficit p K X := by
  have h := hc.map_sum_le (t := Finset.univ) (w := fun _ : Fin 6 ↦ (1 / 6 : ℝ))
    (p := fun k ↦ conjugate (permutations k) X) (by intros; norm_num) (by norm_num)
    (fun _ _ ↦ conjugate_mem_entryBox _ hX)
  change tripleDeficit p K (orbitAverage X) ≤ _ at h
  simp only [tripleDeficit_conjugate_six, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, nsmul_eq_mul] at h
  norm_num at h
  linarith

theorem average_parameter_bounds {X : Triple} (hX : X ∈ entryBox) :
    0 < averageOffDiagonal X ∧ -averageDiagonal X / averageOffDiagonal X ∈ Set.Icc (1 / 2) 2 := by
  have hbar := orbitAverage_mem_entryBox hX
  have hd := hbar 0 0
  have ho := hbar 0 1
  rw [orbitAverage_apply] at hd ho
  norm_num [cyclicCenter, abs_le] at hd ho
  have hop : 0 < averageOffDiagonal X := by linarith
  exact ⟨hop, (le_div_iff₀ hop).mpr (by linarith), (div_le_iff₀ hop).mpr (by linarith)⟩

theorem orbitAverage_eq_cyclic (X : Triple) (ho : averageOffDiagonal X ≠ 0) :
    orbitAverage X = ![averageOffDiagonal X • cyclicX (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicY (-averageDiagonal X / averageOffDiagonal X),
      averageOffDiagonal X • cyclicZ (-averageDiagonal X / averageOffDiagonal X)] := by
  ext j i
  rw [orbitAverage_apply]
  fin_cases j <;> fin_cases i <;> norm_num [cyclicX, cyclicY, cyclicZ] <;> field_simp

theorem tripleDeficit_orbitAverage_nonneg {p : ℝ} (hp : 1 < p) {X : Triple} (hX : X ∈ entryBox) :
    0 ≤ tripleDeficit p (cyclicConstant p) (orbitAverage X) := by
  obtain ⟨ho, ht⟩ := average_parameter_bounds hX
  let t := -averageDiagonal X / averageOffDiagonal X
  have ht0 : 0 ≤ t := by dsimp [t]; linarith [ht.1]
  have hratio := cyclicRatio_le_constant hp ht
  have hD := cyclic_denominator_pos hp ht0
  rw [cyclicRatio, div_le_iff₀ hD] at hratio
  have hcyclic : 0 ≤ hlawkaDeficit p (cyclicConstant p) (cyclicX t) (cyclicY t) (cyclicZ t) := by
    rw [hlawkaDeficit_eq, cyclic_tripleGap (zero_lt_one.trans hp) ht0, cyclic_pairGapSum ht0]
    exact sub_nonneg.mpr hratio
  rw [orbitAverage_eq_cyclic X ho.ne']
  change 0 ≤ hlawkaDeficit p (cyclicConstant p) (averageOffDiagonal X • cyclicX t)
    (averageOffDiagonal X • cyclicY t) (averageOffDiagonal X • cyclicZ t)
  rw [hlawkaDeficit_smul (zero_lt_one.trans hp)]
  exact mul_nonneg (abs_nonneg _) hcyclic

theorem tripleDeficit_nonneg_of_convex {p : ℝ} (hp : 1 < p)
    (hc : ConvexOn ℝ entryBox (tripleDeficit p (cyclicConstant p)))
    {X : Triple} (hX : X ∈ entryBox) : 0 ≤ tripleDeficit p (cyclicConstant p) X :=
  (tripleDeficit_orbitAverage_nonneg hp hX).trans (tripleDeficit_orbitAverage_le hc hX)

/-- Localization and convexity suffice for the real three-coordinate bound. -/
theorem real_bound_of_box_convex {p : ℝ} (hp : 1 < p)
    (hlocal : ∀ x y z : Fin 3 → ℝ,
      hlawkaDeficit p (cyclicConstant p) x y z < 0 →
        ∃ X ∈ entryBox, tripleDeficit p (cyclicConstant p) X < 0)
    (hc : ConvexOn ℝ entryBox (tripleDeficit p (cyclicConstant p))) :
    HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p) := by
  intro x y z
  by_contra hn
  have hf : hlawkaDeficit p (cyclicConstant p) x y z < 0 := by
    rw [hlawkaDeficit_eq]
    linarith
  obtain ⟨X, hX, hneg⟩ := hlocal x y z hf
  exact (not_lt_of_ge (tripleDeficit_nonneg_of_convex hp hc hX)) hneg

section CircleTransfer

instance circleMeasure_isProbability : IsProbabilityMeasure circleMeasure :=
  ⟨by simpa only [TopologicalSpace.PositiveCompacts.coe_top] using
    (Measure.haarMeasure_self (K₀ := (⊤ : TopologicalSpace.PositiveCompacts Circle)))⟩

theorem continuous_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    Continuous (fun u : Circle ↦ |((u : ℂ) * z).re| ^ p) := by
  exact ((Complex.continuous_re.comp (continuous_subtype_val.mul continuous_const)).abs).rpow_const
    (fun _ ↦ Or.inr hp.le)

theorem circleMoment_pos {p : ℝ} (hp : 0 < p) : 0 < circleMoment p := by
  have hc : Continuous (fun u : Circle ↦ |(u : ℂ).re| ^ p) := by
    simpa only [mul_one] using continuous_circle_projection_power hp 1
  exact integral_pos_of_integrable_nonneg_nonzero hc
    (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
    (fun u ↦ Real.rpow_nonneg (abs_nonneg _) _) (x := (1 : Circle)) (by simp)

theorem integral_circle_projection_power {p : ℝ} (hp : 0 < p) (z : ℂ) :
    (∫ u : Circle, |((u : ℂ) * z).re| ^ p ∂circleMeasure) = circleMoment p * ‖z‖ ^ p := by
  by_cases hz : z = 0
  · simp [hz, hp.ne']
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  let v : Circle := ⟨z / (‖z‖ : ℂ), mem_sphere_zero_iff_norm.mpr (by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn])⟩
  have hv : (v : ℂ) * (‖z‖ : ℂ) = z := div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hn)
  have hre (u : Circle) : ((u : ℂ) * z).re = ‖z‖ * ((v * u : Circle) : ℂ).re := by
    calc
      _ = (((v : ℂ) * (u : ℂ)) * (‖z‖ : ℂ)).re := by
        congr 1
        conv_lhs => rw [← hv]
        ring
      _ = _ := by simp only [Circle.coe_mul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, mul_zero, sub_zero]; ring
  simp_rw [hre, abs_mul, abs_of_nonneg (norm_nonneg z),
    Real.mul_rpow (norm_nonneg z) (abs_nonneg _)]
  rw [integral_const_mul]
  have hrot : (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = circleMoment p :=
    integral_mul_left_eq_self (μ := circleMeasure) (fun a : Circle ↦ |(a : ℂ).re| ^ p) v
  change ‖z‖ ^ p * (∫ a : Circle, |((v * a : Circle) : ℂ).re| ^ p ∂circleMeasure) = _
  rw [hrot]
  exact mul_comm _ _

variable {ι : Type*} [Fintype ι]

theorem continuous_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    Continuous (projectionPower p z) :=
  continuous_finsetSum _ fun i _ ↦ continuous_circle_projection_power hp (z i)

theorem integral_projectionPower {p : ℝ} (hp : 0 < p) (z : ι → ℂ) :
    (∫ u : Circle, projectionPower p z u ∂circleMeasure) = circleMoment p * ∑ i, ‖z i‖ ^ p := by
  unfold projectionPower
  rw [integral_finsetSum Finset.univ (fun i _ ↦
    (continuous_circle_projection_power hp (z i)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _))]
  simp only [integral_circle_projection_power hp, Finset.mul_sum]

variable {κ : Type*} [Fintype κ]

omit [Fintype ι] [Fintype κ] in
theorem finiteProjection_add (p : ℝ) (w : κ → ℝ) (u : κ → Circle) (z v : ι → ℂ) :
    finiteProjection p w u (z + v) = finiteProjection p w u z + finiteProjection p w u v := by
  ext k
  simp [finiteProjection, mul_add, Complex.add_re]

theorem lpNorm_finiteProjection {p : ℝ} (hp : 0 < p) (w : κ → ℝ) (u : κ → Circle)
    (hw : ∀ k, 0 ≤ w k) (z : ι → ℂ) :
    _root_.HlawkaSchatten.DiagonalConstruction.lpNorm p (finiteProjection p w u z) = (∑ k, w k * projectionPower p z (u k)) ^ (1 / p) := by
  unfold _root_.HlawkaSchatten.DiagonalConstruction.lpNorm
  congr 1
  simp only [finiteProjection, Fintype.sum_prod_type, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (hw _) _)]
  simp_rw [Real.mul_rpow (Real.rpow_nonneg (hw _) _) (abs_nonneg _),
    ← Real.rpow_mul (hw _), one_div_mul_cancel hp.ne', Real.rpow_one]
  simp only [projectionPower, Finset.mul_sum]

theorem continuous_powerDeficit {p : ℝ} (hp : 0 < p) (K : ℝ) : Continuous (powerDeficit p K) := by
  have hc (i : Fin 7) : Continuous (fun a : Fin 7 → ℝ ↦ (a i) ^ (1 / p)) :=
    (continuous_apply i).rpow_const (fun _ ↦ Or.inr (one_div_nonneg.mpr hp.le))
  exact ((continuous_const.mul (((hc 0).add (hc 1)).add (hc 2))).add (hc 6)).sub
    (continuous_const.mul (((hc 3).add (hc 4)).add (hc 5)))

theorem continuous_sevenProjections {p : ℝ} (hp : 0 < p) (x y z : ι → ℂ) :
    Continuous (sevenProjections p x y z) :=
  continuous_pi fun k ↦ continuous_projectionPower hp (sevenVectors x y z k)

theorem powerDeficit_nonneg_on_projection_hull {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) (x y z : ι → ℂ) :
    convexHull ℝ (Set.range (sevenProjections p x y z)) ⊆
      {a | 0 ≤ powerDeficit p (cyclicConstant p) a} := by
  classical
  intro a ha
  have hp0 : 0 < p := by linarith
  obtain ⟨κ, _, w, points, hw, _, hpoints, hsum⟩ := mem_convexHull_iff_exists_fintype.mp ha
  choose u hu using hpoints
  have hsum' : ∑ k, w k • sevenProjections p x y z (u k) = a := by
    simpa only [hu] using hsum
  let R : (ι → ℂ) → κ × ι → ℝ := finiteProjection p w u
  have hadd (v v' : ι → ℂ) : R (v + v') = R v + R v' := finiteProjection_add p w u v v'
  have hn (k : Fin 7) : lpNorm p (R (sevenVectors x y z k)) = (a k) ^ (1 / p) := by
    rw [lpNorm_finiteProjection hp0 w u hw]
    congr 1
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sevenProjections] using
      congrFun hsum' k
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have h5 := hn 5
  have h6 := hn 6
  change lpNorm p (R x) = (a 0) ^ (1 / p) at h0
  change lpNorm p (R y) = (a 1) ^ (1 / p) at h1
  change lpNorm p (R z) = (a 2) ^ (1 / p) at h2
  change lpNorm p (R (x + y)) = (a 3) ^ (1 / p) at h3
  change lpNorm p (R (x + z)) = (a 4) ^ (1 / p) at h4
  change lpNorm p (R (y + z)) = (a 5) ^ (1 / p) at h5
  change lpNorm p (R (x + y + z)) = (a 6) ^ (1 / p) at h6
  have h := real_bound_of_fin_three hp (by linarith [one_le_cyclicConstant hp]) hreal (R x) (R y) (R z)
  simp only [tripleGap, pairGapSum, pairGap, ← hadd] at h
  change 0 ≤ powerDeficit p (cyclicConstant p) a
  unfold powerDeficit
  rw [← h0, ← h1, ← h2, ← h3, ← h4, ← h5, ← h6]
  nlinarith

/-- The sharp constant passes from real coordinates to complex coordinates. -/
theorem complex_hlawka_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    HasHlawkaConstant (lpNorm p : (ι → ℂ) → ℝ) (cyclicConstant p) := by
  intro x y z
  have hp0 : 0 < p := by linarith
  let F := sevenProjections p x y z
  let m : Fin 7 → ℝ := ∫ u : Circle, F u ∂circleMeasure
  have hcont : Continuous F := continuous_sevenProjections hp0 x y z
  have hfi : Integrable F circleMeasure :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hm : m ∈ closure (convexHull ℝ (Set.range F)) := by
    apply (convex_convexHull ℝ (Set.range F)).closure.integral_mem isClosed_closure _ hfi
    exact Filter.Eventually.of_forall fun u ↦
      subset_closure (subset_convexHull ℝ (Set.range F) (Set.mem_range_self u))
  have hclosed : IsClosed {a | 0 ≤ powerDeficit p (cyclicConstant p) a} :=
    isClosed_le continuous_const (continuous_powerDeficit hp0 _)
  have hnon : 0 ≤ powerDeficit p (cyclicConstant p) m :=
    (closure_minimal (powerDeficit_nonneg_on_projection_hull hp hreal x y z) hclosed) hm
  have hcoord (k : Fin 7) : m k = circleMoment p * ∑ i, ‖sevenVectors x y z k i‖ ^ p := by
    calc
      _ = ∫ u : Circle, F u k ∂circleMeasure :=
        ((ContinuousLinearMap.proj k : (Fin 7 → ℝ) →L[ℝ] ℝ).integral_comp_comm hfi).symm
      _ = _ := integral_projectionPower hp0 (sevenVectors x y z k)
  let c := circleMoment p ^ (1 / p)
  have hc : 0 < c := Real.rpow_pos_of_pos (circleMoment_pos hp0) _
  have hroot (k : Fin 7) : (m k) ^ (1 / p) = c * lpNorm p (sevenVectors x y z k) := by
    rw [hcoord, Real.mul_rpow (circleMoment_pos hp0).le
      (Finset.sum_nonneg fun i _ ↦ Real.rpow_nonneg (norm_nonneg _) _)]
    rfl
  simp only [powerDeficit, hroot] at hnon
  change 0 ≤ (2 * cyclicConstant p - 1) *
      (c * lpNorm p x + c * lpNorm p y + c * lpNorm p z) + c * lpNorm p (x + y + z) -
    cyclicConstant p * (c * lpNorm p (x + y) + c * lpNorm p (x + z) + c * lpNorm p (y + z)) at hnon
  have hscaled : 0 ≤ c * (cyclicConstant p * pairGapSum (lpNorm p) x y z -
      tripleGap (lpNorm p) x y z) := by
    convert hnon using 1
    unfold pairGapSum pairGap tripleGap
    ring
  exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_left hc).mp hscaled)

end CircleTransfer

/-- A real bound in dimension three gives uniform complex sharpness,
including the empty coordinate dimension. -/
theorem isLeast_of_real_bound {p : ℝ} (hp : 1 < p)
    (hreal : HasHlawkaConstant (lpNorm p : (Fin 3 → ℝ) → ℝ) (cyclicConstant p)) :
    IsLeast {C : ℝ | ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C} (cyclicConstant p) := by
  constructor
  · intro n
    exact complex_hlawka_bound hp hreal
  · intro C hC
    exact cyclicConstant_le_of_complex_constant hp (n := 3) (by rfl) (hC 3)

end Cutoff87Integration

open HlawkaSchatten HlawkaSchatten.DiagonalConstruction


theorem solution :
    ∀ p : ℝ, 87 ≤ p → ∀ n : ℕ,
      HasHlawkaConstant (lpNorm p : (Fin n → ℝ) → ℝ)
        (cyclicConstant p) := by
  intro p hp n
  by_cases h88 : 88 ≤ p
  · exact HlawkaSchatten.DiagonalCutoff.real_bound88 p h88 n
  have hp' : p ≤ 88 := by linarith
  have hp1 : 1 < p := by linarith
  have hlinear := cutoff87_cyclicConstant_gt_linear hp hp'
  have hK : 1 ≤ cyclicConstant p := by linarith
  have hKp := cyclicConstant_le_exponent hp1
  have hreal := Cutoff87Integration.real_bound_of_box_convex hp1
    (HlawkaSchatten.DiagonalCutoff87.cutoff87_exists_failure_in_entryBox hp hlinear
      (cutoff87_envelope_lt hp hp'))
    (cutoff87_convexOn_tripleDeficit hp hK hKp)
  exact real_bound_of_fin_three hp1 (by linarith) hreal
