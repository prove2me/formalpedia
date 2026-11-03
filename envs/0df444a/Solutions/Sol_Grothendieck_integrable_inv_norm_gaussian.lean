-- Prove2me | solution 1 for Grothendieck.integrable_inv_norm_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-02T14:23:54.577692+00:00
-- url     : https://prove2.me/submissions/cba5d227-7279-4485-b3b7-8466f62217cf

import Mathlib

set_option autoImplicit false

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Real Topology ENNReal NNReal Interval

namespace GrothendieckPair

/-! ## One-dimensional Gaussian facts

The analysis behind the `r ≥ 2` threshold in Lemma 2.1 is one-dimensional: every
singular factor `‖x‖⁻¹` is controlled by products of one-dimensional factors
`|x i|^(-1/2)`, each of which is integrable against `gaussianReal 0 1`.
-/

lemma gaussianPDFReal_zero_one_apply (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(x ^ 2) / 2) := by
  rw [ProbabilityTheory.gaussianPDFReal_def]
  norm_num

/-- Integration against the standard Gaussian, written through its Lebesgue density. -/
lemma integral_gaussianReal_zero_one_eq (f : ℝ → ℝ) :
    ∫ x, f x ∂(gaussianReal 0 1) = ∫ x, gaussianPDFReal 0 1 x * f x := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integral_withDensity_eq_integral_toReal_smul (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top) f]
  simp only [ProbabilityTheory.gaussianPDF.eq_1,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 _), smul_eq_mul]

lemma integral_zero_L_rpow_neg_half {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (0:ℝ)..L, x ^ (-(1/2) : ℝ) = 2 * Real.sqrt L := by
  rw [integral_rpow (Or.inl (by norm_num : (-1:ℝ) < -(1/2)))]
  rw [show (-(1/2:ℝ) + 1) = 1/2 by norm_num,
    Real.zero_rpow (by norm_num : (1/2:ℝ) ≠ 0), ← Real.sqrt_eq_rpow]
  ring

lemma integral_zero_L_abs_rpow_neg_half {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (0:ℝ)..L, |x| ^ (-(1/2) : ℝ) = 2 * Real.sqrt L := by
  rw [← integral_zero_L_rpow_neg_half hL]
  refine intervalIntegral.integral_congr ?_
  intro x hx
  rw [Set.uIcc_of_le hL] at hx
  show |x| ^ (-(1/2) : ℝ) = x ^ (-(1/2) : ℝ)
  rw [abs_of_nonneg hx.1]

lemma integral_neg_L_zero_abs_rpow_neg_half {L : ℝ} (hL : 0 ≤ L) :
    ∫ x in (-L)..(0:ℝ), |x| ^ (-(1/2) : ℝ) = 2 * Real.sqrt L := by
  have h := intervalIntegral.integral_comp_neg (f := fun x : ℝ => |x| ^ (-(1/2) : ℝ))
    (a := -L) (b := 0)
  simp only [neg_zero, neg_neg, abs_neg] at h
  rw [h, integral_zero_L_abs_rpow_neg_half hL]

/-- `y ↦ |y - c|^(-1/2)` is measurable. -/
lemma measurable_abs_sub_rpow_neg_half (c : ℝ) :
    Measurable (fun y : ℝ => |y - c| ^ (-(1/2) : ℝ)) := by
  have h : (fun y : ℝ => |y - c| ^ (-(1/2) : ℝ)) = fun y => (Real.sqrt |y - c|)⁻¹ := by
    funext y
    rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
  rw [h]
  fun_prop

/-- For `x < 0`, `x^y` has a factor `cos (yπ)`; at `y = -1/2` it vanishes, which makes
`x ↦ |x|^(-1/2)` the sum of two interval-integrable pieces. -/
lemma abs_rpow_neg_half_eq (x : ℝ) :
    |x| ^ (-(1/2) : ℝ) = x ^ (-(1/2) : ℝ) + (-x) ^ (-(1/2) : ℝ) := by
  have hcos : Real.cos (-(1/2:ℝ) * Real.pi) = 0 := by
    rw [show -(1/2:ℝ) * Real.pi = -(Real.pi / 2) by ring, Real.cos_neg, Real.cos_pi_div_two]
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [abs_of_neg hx, Real.rpow_def_of_neg hx, hcos, mul_zero, zero_add]
  · subst hx; simp
  · rw [abs_of_pos hx, Real.rpow_def_of_neg (neg_neg_of_pos hx), hcos, mul_zero, add_zero]

/-- `x ↦ |x|^(-1/2)` is integrable on every `uIoc` interval. -/
lemma integrableOn_abs_rpow_neg_half_any (a b : ℝ) :
    IntegrableOn (fun x : ℝ => |x| ^ (-(1/2) : ℝ)) (Ι a b) volume := by
  have h1 : IntegrableOn (fun x : ℝ => x ^ (-(1/2) : ℝ)) (Ι a b) volume :=
    intervalIntegrable_iff.mp
      (intervalIntegral.intervalIntegrable_rpow' (r := (-(1/2) : ℝ)) (by norm_num))
  have h2 : IntegrableOn (fun x : ℝ => (-x) ^ (-(1/2) : ℝ)) (Ι a b) volume := by
    have h' : IntervalIntegrable (fun x : ℝ => (-x) ^ (-(1/2) : ℝ)) volume a b := by
      simpa only [neg_neg] using
        (IntervalIntegrable.iff_comp_neg (f := fun x : ℝ => x ^ (-(1/2) : ℝ))
          (a := -a) (b := -b) (h := by finiteness)).mp
          (intervalIntegral.intervalIntegrable_rpow' (r := (-(1/2) : ℝ)) (by norm_num))
    exact intervalIntegrable_iff.mp h'
  refine (h1.add h2).congr_fun ?_ measurableSet_uIoc
  intro x _
  exact (abs_rpow_neg_half_eq x).symm

/-- `x ↦ |x|^(-1/2)` is interval integrable on every interval. -/
lemma intervalIntegrable_abs_rpow_neg_half_any (a b : ℝ) :
    IntervalIntegrable (fun x : ℝ => |x| ^ (-(1/2) : ℝ)) volume a b :=
  intervalIntegrable_iff.mpr (integrableOn_abs_rpow_neg_half_any a b)

lemma integral_neg_L_L_abs_rpow_neg_half {L : ℝ} (hL : 0 < L) :
    ∫ x in (-L)..L, |x| ^ (-(1/2) : ℝ) = 4 * Real.sqrt L := by
  have h1 : IntervalIntegrable (fun x : ℝ => |x| ^ (-(1/2) : ℝ)) volume (-L) 0 :=
    intervalIntegrable_abs_rpow_neg_half_any _ _
  have h2 : IntervalIntegrable (fun x : ℝ => |x| ^ (-(1/2) : ℝ)) volume 0 L :=
    intervalIntegrable_abs_rpow_neg_half_any _ _
  have h := intervalIntegral.integral_add_adjacent_intervals h1 h2
  rw [integral_neg_L_zero_abs_rpow_neg_half hL.le,
    integral_zero_L_abs_rpow_neg_half hL.le] at h
  rw [← h]; ring

lemma integral_abs_sub_rpow_neg_half {c L : ℝ} (hL : 0 < L) :
    ∫ y in (c - L)..(c + L), |y - c| ^ (-(1/2) : ℝ) = 4 * Real.sqrt L := by
  have h := intervalIntegral.integral_comp_add_right (f := fun z : ℝ => |z| ^ (-(1/2) : ℝ))
    (a := c - L) (b := c + L) (d := -c)
  rw [show c - L + -c = -L by ring, show c + L + -c = L by ring] at h
  simp only [sub_eq_add_neg] at h ⊢
  rw [h]
  exact integral_neg_L_L_abs_rpow_neg_half hL

lemma integrableOn_abs_sub_rpow_neg_half {c L : ℝ} (hL : 0 < L) :
    IntegrableOn (fun y : ℝ => |y - c| ^ (-(1/2) : ℝ)) (Set.Icc (c - L) (c + L)) volume := by
  rw [← intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : c - L ≤ c + L)]
  have h := (intervalIntegrable_abs_rpow_neg_half_any (-L) L).comp_sub_right c
  simpa only [neg_add_eq_sub, add_comm, sub_eq_add_neg] using h

/-- The truncated singular factor `y ↦ |y - c|^(-1/2) 1_{|y - c| ≤ L}`. -/
def trunc (c L : ℝ) (y : ℝ) : ℝ :=
  (Set.Icc (c - L) (c + L)).indicator (fun y => |y - c| ^ (-(1/2) : ℝ)) y

lemma trunc_nonneg (c L y : ℝ) : 0 ≤ trunc c L y := by
  rw [trunc, Set.indicator_apply]; split_ifs
  · exact Real.rpow_nonneg (abs_nonneg _) _
  · exact le_refl 0

lemma trunc_eq_indicator (c L : ℝ) :
    trunc c L = (Set.Icc (c - L) (c + L)).indicator (fun y => |y - c| ^ (-(1/2) : ℝ)) := rfl

lemma measurable_trunc (c L : ℝ) : Measurable (trunc c L) := by
  rw [trunc_eq_indicator]
  exact (measurable_abs_sub_rpow_neg_half c).indicator measurableSet_Icc

lemma integrable_trunc_volume {c L : ℝ} (hL : 0 < L) : Integrable (trunc c L) volume := by
  rw [trunc_eq_indicator, integrable_indicator_iff measurableSet_Icc]
  exact integrableOn_abs_sub_rpow_neg_half hL

lemma integral_trunc_volume {c L : ℝ} (hL : 0 < L) :
    ∫ y, trunc c L y ∂volume = 4 * Real.sqrt L := by
  rw [trunc_eq_indicator]
  rw [integral_indicator measurableSet_Icc]
  rw [integral_Icc_eq_integral_Ioc]
  rw [← intervalIntegral.integral_of_le (by linarith : c - L ≤ c + L)]
  exact integral_abs_sub_rpow_neg_half hL

lemma exp_neg_sq_div_two_le_one (y : ℝ) : Real.exp (-(y ^ 2) / 2) ≤ 1 := by
  rw [← Real.exp_zero]
  exact Real.exp_le_exp.mpr (by nlinarith [sq_nonneg y])

lemma gaussianPDFReal_zero_one_le (y : ℝ) :
    gaussianPDFReal 0 1 y ≤ (Real.sqrt (2 * Real.pi))⁻¹ := by
  rw [gaussianPDFReal_zero_one_apply]
  calc (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(y ^ 2) / 2)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * 1 :=
        mul_le_mul_of_nonneg_left (exp_neg_sq_div_two_le_one y) (by positivity)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ := mul_one _

lemma gaussianPDF_toReal_smul (y : ℝ) (z : ℝ) :
    (gaussianPDF 0 1 y).toReal • z = gaussianPDFReal 0 1 y * z := by
  rw [ProbabilityTheory.gaussianPDF.eq_1,
    ENNReal.toReal_ofReal (gaussianPDFReal_nonneg 0 1 y), smul_eq_mul]

lemma integrable_trunc_gaussianReal {c L : ℝ} (hL : 0 < L) :
    Integrable (trunc c L) (gaussianReal 0 1) := by
  rw [ProbabilityTheory.gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0)]
  rw [integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF 0 1)
    (by filter_upwards with x; exact ENNReal.ofReal_lt_top)]
  rw [show (fun y => (gaussianPDF 0 1 y).toReal • trunc c L y)
      = fun y => gaussianPDFReal 0 1 y * trunc c L y from
    funext fun y => gaussianPDF_toReal_smul y (trunc c L y)]
  refine Integrable.mono' (g := fun y => (Real.sqrt (2 * Real.pi))⁻¹ * trunc c L y)
    ((integrable_trunc_volume hL).const_mul _)
    ((measurable_gaussianPDFReal 0 1).mul (measurable_trunc c L)).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg 0 1 y) (trunc_nonneg c L y))]
  exact mul_le_mul_of_nonneg_right (gaussianPDFReal_zero_one_le y) (trunc_nonneg c L y)

/-- **Truncated bound**: for every centre `c` and radius `L > 0`,
`∫ |y-c|^(-1/2) 1_{|y-c| ≤ L} dγ ≤ (4√L)/√(2π)`. -/
lemma integral_trunc_gaussian_le {c L : ℝ} (hL : 0 < L) :
    ∫ y, trunc c L y ∂(gaussianReal 0 1)
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (4 * Real.sqrt L) := by
  have hvol : Integrable (trunc c L) volume := integrable_trunc_volume hL
  rw [integral_gaussianReal_zero_one_eq]
  have hcongr : (fun y : ℝ => gaussianPDFReal 0 1 y * trunc c L y)
      = fun y => (Real.sqrt (2 * Real.pi))⁻¹ *
          (Real.exp (-(y ^ 2) / 2) * trunc c L y) := by
    funext y; rw [gaussianPDFReal_zero_one_apply]; ring
  rw [hcongr, integral_const_mul]
  have hexpF : Integrable (fun y : ℝ => Real.exp (-(y ^ 2) / 2) * trunc c L y) volume := by
    refine hvol.mono' ((Real.continuous_exp.comp (by fun_prop)).measurable.mul
      (measurable_trunc c L)).aestronglyMeasurable ?_
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (trunc_nonneg c L y))]
    calc Real.exp (-(y ^ 2) / 2) * trunc c L y ≤ 1 * trunc c L y :=
          mul_le_mul_of_nonneg_right (exp_neg_sq_div_two_le_one y) (trunc_nonneg c L y)
      _ = trunc c L y := one_mul _
  have hle : ∫ y, Real.exp (-(y ^ 2) / 2) * trunc c L y ≤ ∫ y, trunc c L y := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall (fun y => ?_)) hvol
      (Filter.Eventually.of_forall (fun y => ?_))
    · exact mul_nonneg (Real.exp_pos _).le (trunc_nonneg c L y)
    · calc Real.exp (-(y ^ 2) / 2) * trunc c L y ≤ 1 * trunc c L y :=
            mul_le_mul_of_nonneg_right (exp_neg_sq_div_two_le_one y) (trunc_nonneg c L y)
        _ = trunc c L y := one_mul _
  calc (Real.sqrt (2 * Real.pi))⁻¹ * ∫ y, Real.exp (-(y ^ 2) / 2) * trunc c L y
      ≤ (Real.sqrt (2 * Real.pi))⁻¹ * ∫ y, trunc c L y :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = (Real.sqrt (2 * Real.pi))⁻¹ * (4 * Real.sqrt L) := by
        rw [integral_trunc_volume hL]

/-- **Shifted one-dimensional integrability**: `y ↦ |y - c|^(-1/2)` is integrable
against the standard Gaussian, for every centre `c`. -/
lemma integrable_abs_sub_rpow_neg_half_gaussianReal (c : ℝ) :
    Integrable (fun y : ℝ => |y - c| ^ (-(1/2) : ℝ)) (gaussianReal 0 1) := by
  have htrunc : Integrable (trunc c 1) (gaussianReal 0 1) :=
    integrable_trunc_gaussianReal one_pos
  have hmain : ∀ y : ℝ, |y - c| ^ (-(1/2) : ℝ) ≤ 1 + trunc c 1 y := by
    intro y
    by_cases h : |y - c| ≤ 1
    · have hmem : y ∈ Set.Icc (c - 1) (c + 1) := by
        rw [Set.mem_Icc]
        rw [abs_le] at h
        constructor <;> linarith [h.1, h.2]
      have : trunc c 1 y = |y - c| ^ (-(1/2) : ℝ) := by
        rw [trunc, Set.indicator_of_mem hmem]
      rw [this]
      linarith [Real.rpow_nonneg (abs_nonneg (y - c)) (-(1/2) : ℝ)]
    · push_neg at h
      have h0 : |y - c| ^ (-(1/2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h.le (by norm_num)
      linarith [trunc_nonneg c 1 y]
  refine Integrable.mono' ((integrable_const (1:ℝ)).add htrunc)
    (measurable_abs_sub_rpow_neg_half c).aestronglyMeasurable ?_
  filter_upwards with y
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact hmain y


/-! ## The `r`-dimensional statement -/

/-- AM-GM: `(a²+b²)^(-1/2) ≤ |a|^(-1/2)·|b|^(-1/2)`. -/
lemma amgm_two {a b : ℝ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a ^ 2 + b ^ 2) ^ (-(1/2) : ℝ) ≤ |a| ^ (-(1/2) : ℝ) * |b| ^ (-(1/2) : ℝ) := by
  have hsum : 0 < a ^ 2 + b ^ 2 := by positivity
  have ha' : 0 < |a| := abs_pos.mpr ha
  have hb' : 0 < |b| := abs_pos.mpr hb
  have hle : |a| * |b| ≤ a ^ 2 + b ^ 2 := by
    nlinarith [sq_abs a, sq_abs b, sq_nonneg (|a| - |b|)]
  rw [Real.rpow_neg (le_of_lt hsum), Real.rpow_neg (le_of_lt ha'),
    Real.rpow_neg (le_of_lt hb'), ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow,
    ← Real.sqrt_eq_rpow, ← mul_inv, ← Real.sqrt_mul (le_of_lt ha')]
  exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (Real.sqrt_le_sqrt hle)

/-- The sum of squares of two distinct coordinates is at most the full sum. -/
lemma two_coord_sum_le {r : ℕ} (x : Fin r → ℝ) {i0 i1 : Fin r} (hne : i0 ≠ i1) :
    x i0 ^ 2 + x i1 ^ 2 ≤ ∑ i, x i ^ 2 := by
  classical
  have h1 : x i0 ^ 2 ≤ ∑ i, x i ^ 2 :=
    Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) (Finset.mem_univ i0)
  have hmem : i1 ∈ Finset.univ.erase i0 :=
    Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ i1⟩
  have h2 : x i1 ^ 2 ≤ ∑ i ∈ Finset.univ.erase i0, x i ^ 2 :=
    Finset.single_le_sum (f := fun i => x i ^ 2) (fun i _ => sq_nonneg (x i)) hmem
  have hsplit : ∑ i, x i ^ 2 = x i0 ^ 2 + ∑ i ∈ Finset.univ.erase i0, x i ^ 2 :=
    (Finset.add_sum_erase Finset.univ (fun i => x i ^ 2) (Finset.mem_univ i0)).symm
  linarith

/-- Measurability of a single coordinate factor. -/
lemma measurable_coord_abs_rpow_neg_half {r : ℕ} (i : Fin r) :
    Measurable (fun x : Fin r → ℝ => |x i| ^ (-(1/2) : ℝ)) := by
  have h : Measurable (fun x : Fin r → ℝ => |x i - 0| ^ (-(1/2) : ℝ)) :=
    (measurable_abs_sub_rpow_neg_half (0:ℝ)).comp (measurable_pi_apply i)
  simpa using h

/-- Measurability of the norm factor. -/
lemma measurable_inv_norm_pi {r : ℕ} :
    Measurable (fun x : Fin r → ℝ => (∑ i, x i ^ 2) ^ (-(1/2) : ℝ)) := by
  have h : (fun x : Fin r → ℝ => (∑ i, x i ^ 2) ^ (-(1/2) : ℝ))
      = fun x => (Real.sqrt (∑ i, x i ^ 2))⁻¹ := by
    funext x
    rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
  rw [h]
  fun_prop

/-- **The `r`-dimensional standard Gaussian case**: for `r ≥ 2`,
`x ↦ ‖x‖⁻¹` is integrable against the product of `r` standard Gaussians. -/
theorem integrable_inv_norm_pi_proof (r : ℕ) (hr : 2 ≤ r) :
    Integrable (fun x : Fin r → ℝ => (∑ i, x i ^ 2) ^ (-(1/2) : ℝ))
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) := by
  classical
  haveI hNull : NullSingletonClass (gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  set i0 : Fin r := ⟨0, by omega⟩ with hi0def
  set i1 : Fin r := ⟨1, by omega⟩ with hi1def
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [hi0def, hi1def] at this
  have hbase : Integrable (fun t : ℝ => |t| ^ (-(1/2) : ℝ)) (gaussianReal 0 1) := by
    simpa using integrable_abs_sub_rpow_neg_half_gaussianReal 0
  set F : Fin r → ℝ → ℝ := fun i => if i = i0 ∨ i = i1 then fun t => |t| ^ (-(1/2) : ℝ) else 1
    with hFdef
  have hFi : ∀ i, Integrable (F i) (gaussianReal 0 1) := by
    intro i
    by_cases h : i = i0 ∨ i = i1
    · simp only [hFdef, h, if_true]; exact hbase
    · simp only [hFdef, h, if_false]; exact integrable_const 1
  have hprod : Integrable (fun x : Fin r → ℝ => ∏ i, F i (x i))
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) :=
    Integrable.fintype_prod hFi
  have hprodeq : ∀ x : Fin r → ℝ,
      ∏ i, F i (x i) = |x i0| ^ (-(1/2) : ℝ) * |x i1| ^ (-(1/2) : ℝ) := by
    intro x
    have hsub : ({i0, i1} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.prod_subset hsub (fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp only [hFdef]
      rw [if_neg (by tauto), Pi.one_apply])]
    rw [Finset.prod_pair hne]
    have h1 : F i0 (x i0) = |x i0| ^ (-(1/2) : ℝ) := by rw [hFdef]; simp
    have h2 : F i1 (x i1) = |x i1| ^ (-(1/2) : ℝ) := by rw [hFdef]; simp
    rw [h1, h2]
  have hprod' : Integrable
      (fun x : Fin r → ℝ => |x i0| ^ (-(1/2) : ℝ) * |x i1| ^ (-(1/2) : ℝ))
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) :=
    hprod.congr (Filter.Eventually.of_forall fun x => hprodeq x)
  refine Integrable.mono' hprod' ?_ ?_
  · exact measurable_inv_norm_pi.aestronglyMeasurable
  · filter_upwards [Measure.ae_eval_ne (μ := fun _ : Fin r => gaussianReal 0 1) i0 (0 : ℝ),
      Measure.ae_eval_ne (μ := fun _ : Fin r => gaussianReal 0 1) i1 (0 : ℝ)] with x hx0 hx1
    rw [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ => sq_nonneg (x i))) _)]
    have hle : x i0 ^ 2 + x i1 ^ 2 ≤ ∑ i, x i ^ 2 := two_coord_sum_le x hne
    have hpos : 0 < x i0 ^ 2 + x i1 ^ 2 := by
      have h := abs_pos.mpr hx0
      nlinarith [sq_abs (x i0), sq_nonneg (x i1)]
    have hsum_pos : 0 < ∑ i, x i ^ 2 := lt_of_lt_of_le hpos hle
    calc (∑ i, x i ^ 2) ^ (-(1/2) : ℝ)
        ≤ (x i0 ^ 2 + x i1 ^ 2) ^ (-(1/2) : ℝ) := by
          rw [Real.rpow_neg (le_of_lt hsum_pos), Real.rpow_neg (le_of_lt hpos),
            ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
          exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (Real.sqrt_le_sqrt hle)
      _ ≤ |x i0| ^ (-(1/2) : ℝ) * |x i1| ^ (-(1/2) : ℝ) := amgm_two hx0 hx1


/-- **Two independent standard Gaussians**: for `r ≥ 2`, the function
`p ↦ (‖p.1‖ ‖p.2‖)⁻¹` is integrable for the product of two `r`-dimensional
standard Gaussians (Tonelli splitting of the two singular factors). -/
theorem integrable_inv_mul_norm_pi_prod (r : ℕ) (hr : 2 ≤ r) :
    Integrable (fun p : (Fin r → ℝ) × (Fin r → ℝ) =>
      ((∑ i, p.1 i ^ 2) * (∑ i, p.2 i ^ 2)) ^ (-(1/2) : ℝ))
      ((Measure.pi fun _ : Fin r => gaussianReal 0 1).prod
        (Measure.pi fun _ : Fin r => gaussianReal 0 1)) := by
  have h := Integrable.mul_prod (integrable_inv_norm_pi_proof r hr) (integrable_inv_norm_pi_proof r hr)
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  have h1 : 0 ≤ ∑ i, p.1 i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (p.1 i))
  have h2 : 0 ≤ ∑ i, p.2 i ^ 2 := Finset.sum_nonneg (fun i _ => sq_nonneg (p.2 i))
  show (∑ i, p.1 i ^ 2) ^ (-(1/2) : ℝ) * (∑ i, p.2 i ^ 2) ^ (-(1/2) : ℝ)
      = ((∑ i, p.1 i ^ 2) * (∑ i, p.2 i ^ 2)) ^ (-(1/2) : ℝ)
  rw [Real.mul_rpow h1 h2]


/-! ## The correlated row -/

lemma ae_neq_zero_gaussianReal : ∀ᵐ x ∂(gaussianReal 0 1), x ≠ 0 := by
  haveI : NullSingletonClass (gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  rw [MeasureTheory.ae_iff]
  simpa using measure_singleton (0 : ℝ)

/-- Bound on the full (untruncated) singular factor: it is at most `4/√(2π) + 1`. -/
lemma integral_abs_sub_rpow_neg_half_gaussian_le (c : ℝ) :
    ∫ y, |y - c| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1)
      ≤ 4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1 := by
  have hpt : ∀ y : ℝ, |y - c| ^ (-(1/2) : ℝ) ≤ trunc c 1 y + 1 := by
    intro y
    by_cases h : |y - c| ≤ 1
    · have hmem : y ∈ Set.Icc (c - 1) (c + 1) := by
        rw [Set.mem_Icc]
        rw [abs_le] at h
        constructor <;> linarith [h.1, h.2]
      have hy : trunc c 1 y = |y - c| ^ (-(1/2) : ℝ) := by
        rw [trunc, Set.indicator_of_mem hmem]
      rw [hy]
      linarith [trunc_nonneg c 1 y]
    · push Not at h
      have h0 : |y - c| ^ (-(1/2) : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos h.le (by norm_num)
      linarith [trunc_nonneg c 1 y]
  calc ∫ y, |y - c| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1)
      ≤ ∫ y, (trunc c 1 y + 1) ∂(gaussianReal 0 1) :=
        integral_mono (integrable_abs_sub_rpow_neg_half_gaussianReal c)
          ((integrable_trunc_gaussianReal one_pos).add (integrable_const 1)) hpt
    _ = (∫ y, trunc c 1 y ∂(gaussianReal 0 1)) + ∫ _y, (1:ℝ) ∂(gaussianReal 0 1) :=
        integral_add (integrable_trunc_gaussianReal one_pos) (integrable_const 1)
    _ ≤ (Real.sqrt (2 * Real.pi))⁻¹ * (4 * Real.sqrt 1) + 1 := by
        have h := integral_trunc_gaussian_le (c := c) one_pos
        have h1 : ∫ _y, (1:ℝ) ∂(gaussianReal 0 1) = 1 := by simp
        rw [h1]
        linarith
    _ = 4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1 := by
        rw [Real.sqrt_one, mul_one]; ring

lemma measurable_abs_lin_rpow (t s : ℝ) :
    Measurable (fun p : ℝ × ℝ => |t * p.1 + s * p.2| ^ (-(1/2) : ℝ)) := by
  have h : Measurable (fun p : ℝ × ℝ => t * p.1 + s * p.2) := by fun_prop
  have h2 : Measurable (fun p : ℝ × ℝ => |(t * p.1 + s * p.2) - 0| ^ (-(1/2) : ℝ)) :=
    (measurable_abs_sub_rpow_neg_half (0:ℝ)).comp h
  simpa using h2

lemma abs_lin_rpow_eq {t s x y : ℝ} (hs : 0 < s) :
    |t * x + s * y| ^ (-(1/2) : ℝ)
      = s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ) := by
  have h : t * x + s * y = s * (y - (-(t / s) * x)) := by
    field_simp
    ring
  rw [h, abs_mul, abs_of_pos hs, Real.mul_rpow (le_of_lt hs) (abs_nonneg _)]

/-- **The correlated row**: for `|t| < 1`, the product of the two singular coordinate
factors is integrable for `(y₀, t y₀ + √(1-t²) y₁)` with `(y₀,y₁)` standard Gaussian. -/
lemma integrable_correlated_row {t : ℝ} (ht : |t| < 1) :
    Integrable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ) *
      |t * p.1 + Real.sqrt (1 - t ^ 2) * p.2| ^ (-(1/2) : ℝ))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  have hs : 0 < Real.sqrt (1 - t ^ 2) := by
    rw [Real.sqrt_pos]
    have := abs_lt.mp ht
    nlinarith [this.1, this.2]
  set s := Real.sqrt (1 - t^2) with hsdef
  have hK : 0 ≤ s ^ (-(1/2) : ℝ) * (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1) := by positivity
  refine integrable_prod_iff ?_ |>.mpr ⟨?_, ?_⟩
  · -- measurability
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) := by
      have h : (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) = fun p => (Real.sqrt |p.1|)⁻¹ := by
        funext p
        rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
      rw [h]
      fun_prop
    exact h1.mul (measurable_abs_lin_rpow t s)
  · -- a.e. inner integrability
    filter_upwards [ae_neq_zero_gaussianReal] with x hx
    have hc : ∀ y : ℝ, |t * x + s * y| ^ (-(1/2) : ℝ)
        = s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ) := fun y => abs_lin_rpow_eq hs
    have hbase : Integrable (fun y : ℝ => |y - (-(t / s) * x)| ^ (-(1/2) : ℝ))
        (gaussianReal 0 1) := integrable_abs_sub_rpow_neg_half_gaussianReal _
    have hmul : Integrable (fun y : ℝ => |x| ^ (-(1/2) : ℝ) *
        (s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ))) (gaussianReal 0 1) :=
      (hbase.const_mul (s ^ (-(1/2) : ℝ))).const_mul (|x| ^ (-(1/2) : ℝ))
    refine hmul.congr (Filter.Eventually.of_forall fun y => ?_)
    show |x| ^ (-(1/2) : ℝ) * (s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ))
      = |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ)
    rw [hc y]
  · -- integrability of the inner integral
    have hinner : ∀ x : ℝ, x ≠ 0 →
        (∫ y, |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1))
          ≤ |x| ^ (-(1/2) : ℝ) * (s ^ (-(1/2) : ℝ) * (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1)) := by
      intro x _
      have hc : ∀ y : ℝ, |t * x + s * y| ^ (-(1/2) : ℝ)
          = s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ) := fun y => abs_lin_rpow_eq hs
      calc (∫ y, |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1))
          = |x| ^ (-(1/2) : ℝ) *
              ∫ y, |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1) := by
            rw [integral_const_mul]
        _ = |x| ^ (-(1/2) : ℝ) *
              ∫ y, s ^ (-(1/2) : ℝ) * |y - (-(t / s) * x)| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1) := by
            simp only [hc]
        _ = |x| ^ (-(1/2) : ℝ) * (s ^ (-(1/2) : ℝ) *
              ∫ y, |y - (-(t / s) * x)| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1)) := by
            rw [integral_const_mul]
        _ ≤ |x| ^ (-(1/2) : ℝ) * (s ^ (-(1/2) : ℝ) *
              (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1)) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply mul_le_mul_of_nonneg_left (integral_abs_sub_rpow_neg_half_gaussian_le _) (by positivity)
    have hcongr : (fun x => ∫ y, ‖|x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ)‖
        ∂(gaussianReal 0 1))
        = fun x => ∫ y, |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1) := by
      funext x
      congr 1 with y
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [hcongr]
    have hbase0 : Integrable (fun x : ℝ => |x| ^ (-(1/2) : ℝ)) (gaussianReal 0 1) := by
      simpa using integrable_abs_sub_rpow_neg_half_gaussianReal 0
    refine Integrable.mono'
      (f := fun x => ∫ y, |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1))
      (g := fun x => (s ^ (-(1/2) : ℝ) * (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1)) *
        |x| ^ (-(1/2) : ℝ))
      (hbase0.const_mul _) ?_ ?_
    · -- measurability of the integral function
      have h1 : Measurable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) := by
        have h : (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) = fun p => (Real.sqrt |p.1|)⁻¹ := by
          funext p
          rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
        rw [h]
        fun_prop
      have hmeas : Measurable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ) *
          |t * p.1 + s * p.2| ^ (-(1/2) : ℝ)) := h1.mul (measurable_abs_lin_rpow t s)
      exact (hmeas.stronglyMeasurable.integral_prod_right' (ν := gaussianReal 0 1)).aestronglyMeasurable
    · filter_upwards [ae_neq_zero_gaussianReal] with x hx
      rw [Real.norm_eq_abs,
        abs_of_nonneg (integral_nonneg (fun y => by positivity))]
      calc ∫ y, |x| ^ (-(1/2) : ℝ) * |t * x + s * y| ^ (-(1/2) : ℝ) ∂(gaussianReal 0 1)
          ≤ |x| ^ (-(1/2) : ℝ) * (s ^ (-(1/2) : ℝ) * (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1)) :=
            hinner x hx
        _ = (s ^ (-(1/2) : ℝ) * (4 * (Real.sqrt (2 * Real.pi))⁻¹ + 1)) * |x| ^ (-(1/2) : ℝ) :=
            mul_comm _ _


/-- Combining the two-coordinate AM-GM with the `‖·‖⁻¹` bound. -/
lemma inv_sqrt_sum_le_two {r : ℕ} (x : Fin r → ℝ) {i0 i1 : Fin r} (hne : i0 ≠ i1)
    (hx0 : x i0 ≠ 0) (hx1 : x i1 ≠ 0) :
    (∑ i, x i ^ 2) ^ (-(1/2) : ℝ) ≤ |x i0| ^ (-(1/2) : ℝ) * |x i1| ^ (-(1/2) : ℝ) := by
  have hle : x i0 ^ 2 + x i1 ^ 2 ≤ ∑ i, x i ^ 2 := two_coord_sum_le x hne
  have hpos : 0 < x i0 ^ 2 + x i1 ^ 2 := by
    have h := abs_pos.mpr hx0
    nlinarith [sq_abs (x i0), sq_nonneg (x i1)]
  have hsum_pos : 0 < ∑ i, x i ^ 2 := lt_of_lt_of_le hpos hle
  calc (∑ i, x i ^ 2) ^ (-(1/2) : ℝ)
      ≤ (x i0 ^ 2 + x i1 ^ 2) ^ (-(1/2) : ℝ) := by
        rw [Real.rpow_neg (le_of_lt hsum_pos), Real.rpow_neg (le_of_lt hpos),
          ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
        exact (inv_le_inv₀ (by positivity) (by positivity)).mpr (Real.sqrt_le_sqrt hle)
    _ ≤ |x i0| ^ (-(1/2) : ℝ) * |x i1| ^ (-(1/2) : ℝ) := amgm_two hx0 hx1

/-- **The pair law of `(Zu, Zv)`, in Cholesky coordinates**: for `r ≥ 2`, `|t| < 1`, the
function `(‖X‖ ‖Y‖)⁻¹` is integrable when the `r` rows `(P i).1`, `(P i).2` are independent
standard Gaussians and `X i = (P i).1`, `Y i = t (P i).1 + √(1-t²) (P i).2`. -/
theorem integrable_inv_mul_norm_pair_rows (r : ℕ) (hr : 2 ≤ r) {t : ℝ} (ht : |t| < 1) :
    Integrable (fun P : Fin r → ℝ × ℝ =>
      ((∑ i, (P i).1 ^ 2) * (∑ i, (t * (P i).1 + Real.sqrt (1 - t ^ 2) * (P i).2) ^ 2))
        ^ (-(1/2) : ℝ))
      (Measure.pi fun _ : Fin r => (gaussianReal 0 1).prod (gaussianReal 0 1)) := by
  classical
  haveI hNull : NullSingletonClass (gaussianReal 0 1) :=
    ProbabilityTheory.nullSingletonClass_gaussianReal (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hs : 0 < Real.sqrt (1 - t ^ 2) := by
    rw [Real.sqrt_pos]
    have := abs_lt.mp ht
    nlinarith [this.1, this.2]
  set s := Real.sqrt (1 - t ^ 2) with hsdef
  set ν : Measure (ℝ × ℝ) := (gaussianReal 0 1).prod (gaussianReal 0 1) with hν
  haveI hNullν : NullSingletonClass ν := by
    constructor
    intro p
    have hsub : ({p} : Set (ℝ × ℝ)) ⊆ {q : ℝ × ℝ | q.1 = p.1} := by
      intro q hq
      simp only [Set.mem_singleton_iff] at hq
      simp [hq]
    refine measure_mono_null hsub ?_
    have hset : {q : ℝ × ℝ | q.1 = p.1} = ({p.1} : Set ℝ) ×ˢ Set.univ := by
      ext q; simp
    rw [hν, hset, Measure.prod_prod]
    simp
  set i0 : Fin r := ⟨0, by omega⟩ with hi0def
  set i1 : Fin r := ⟨1, by omega⟩ with hi1def
  have hne : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [hi0def, hi1def] at this
  have hcoord1 : ∀ i : Fin r, ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν), (P i).1 ≠ 0 := by
    intro i
    have hsingle : ν {q : ℝ × ℝ | q.1 = 0} = 0 := by
      have hset : {q : ℝ × ℝ | q.1 = 0} = ({0} : Set ℝ) ×ˢ Set.univ := by ext q; simp
      rw [hν, hset, Measure.prod_prod]
      simp
    have h := Measure.pi_eval_preimage_null (μ := fun _ : Fin r => ν) (i := i) hsingle
    rw [MeasureTheory.ae_iff]
    have h' : {P : Fin r → ℝ × ℝ | ¬ (P i).1 ≠ 0} = {P | P i ∈ {q : ℝ × ℝ | q.1 = 0}} := by
      ext P; simp
    rw [h']
    exact h
  have hcoord2 : ∀ i : Fin r, ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν), (P i).2 ≠ 0 := by
    intro i
    have hsingle : ν {q : ℝ × ℝ | q.2 = 0} = 0 := by
      have hset : {q : ℝ × ℝ | q.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by ext q; simp
      rw [hν, hset, Measure.prod_prod]
      simp
    have h := Measure.pi_eval_preimage_null (μ := fun _ : Fin r => ν) (i := i) hsingle
    rw [MeasureTheory.ae_iff]
    have h' : {P : Fin r → ℝ × ℝ | ¬ (P i).2 ≠ 0} = {P | P i ∈ {q : ℝ × ℝ | q.2 = 0}} := by
      ext P; simp
    rw [h']
    exact h
  -- a.e. non-vanishing of the `y`-coordinates
  have hycoord : ∀ i : Fin r, ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν),
      t * (P i).1 + s * (P i).2 ≠ 0 := by
    intro i
    have hsingle : ν {q : ℝ × ℝ | t * q.1 + s * q.2 = 0} = 0 := by
      have hmeas : MeasurableSet {q : ℝ × ℝ | t * q.1 + s * q.2 = 0} :=
        measurableSet_eq_fun (by fun_prop) measurable_const
      rw [hν, Measure.prod_apply hmeas]
      have hsec : ∀ x : ℝ,
          (gaussianReal 0 1) (Prod.mk x ⁻¹' {q : ℝ × ℝ | t * q.1 + s * q.2 = 0}) = 0 := by
        intro x
        have hset : Prod.mk x ⁻¹' {q : ℝ × ℝ | t * q.1 + s * q.2 = 0}
            = ({-(t * x) / s} : Set ℝ) := by
          ext y
          simp only [Set.mem_preimage, Set.mem_setOf_eq, Set.mem_singleton_iff]
          constructor
          · intro h
            field_simp
            linarith
          · intro h
            rw [h]
            field_simp
            ring
        rw [hset]
        exact measure_singleton _
      simp only [hsec]
      simp
    have h := Measure.pi_eval_preimage_null (μ := fun _ : Fin r => ν) (i := i) hsingle
    rw [MeasureTheory.ae_iff]
    have h' : {P : Fin r → ℝ × ℝ | ¬ t * (P i).1 + s * (P i).2 ≠ 0}
        = {P | P i ∈ {q : ℝ × ℝ | t * q.1 + s * q.2 = 0}} := by
      ext P; simp
    rw [h']
    exact h
  have hx0 : ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν), (P i0).1 ≠ 0 := hcoord1 i0
  have hx1 : ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν), (P i1).1 ≠ 0 := hcoord1 i1
  have hy0 : ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν),
      t * (P i0).1 + s * (P i0).2 ≠ 0 := hycoord i0
  have hy1 : ∀ᵐ P ∂(Measure.pi fun _ : Fin r => ν),
      t * (P i1).1 + s * (P i1).2 ≠ 0 := hycoord i1
  -- the dominating product over the two rows `i0`, `i1`
  set F : Fin r → ℝ × ℝ → ℝ := fun i =>
    if i = i0 ∨ i = i1 then
      fun p => |p.1| ^ (-(1/2) : ℝ) * |t * p.1 + Real.sqrt (1 - t ^ 2) * p.2| ^ (-(1/2) : ℝ)
    else 1 with hFdef
  have hFi : ∀ i, Integrable (F i) ν := by
    intro i
    by_cases h : i = i0 ∨ i = i1
    · simp only [hFdef, h, if_true]
      exact integrable_correlated_row ht
    · simp only [hFdef, h, if_false]
      exact integrable_const 1
  have hprod : Integrable (fun P : Fin r → ℝ × ℝ => ∏ i, F i (P i))
      (Measure.pi fun _ : Fin r => ν) :=
    Integrable.fintype_prod hFi
  have hprodeq : ∀ P : Fin r → ℝ × ℝ,
      ∏ i, F i (P i) = (|(P i0).1| ^ (-(1/2) : ℝ) *
          |t * (P i0).1 + Real.sqrt (1 - t ^ 2) * (P i0).2| ^ (-(1/2) : ℝ)) *
        (|(P i1).1| ^ (-(1/2) : ℝ) *
          |t * (P i1).1 + Real.sqrt (1 - t ^ 2) * (P i1).2| ^ (-(1/2) : ℝ)) := by
    intro P
    have hsub : ({i0, i1} : Finset (Fin r)) ⊆ Finset.univ := Finset.subset_univ _
    rw [← Finset.prod_subset hsub (fun i _ hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi
      simp only [hFdef]
      rw [if_neg (by tauto), Pi.one_apply])]
    rw [Finset.prod_pair hne]
    have h1 : F i0 (P i0) = |(P i0).1| ^ (-(1/2) : ℝ) *
        |t * (P i0).1 + Real.sqrt (1 - t ^ 2) * (P i0).2| ^ (-(1/2) : ℝ) := by
      rw [hFdef]; simp
    have h2 : F i1 (P i1) = |(P i1).1| ^ (-(1/2) : ℝ) *
        |t * (P i1).1 + Real.sqrt (1 - t ^ 2) * (P i1).2| ^ (-(1/2) : ℝ) := by
      rw [hFdef]; simp
    rw [h1, h2]
  have hprod' : Integrable (fun P : Fin r → ℝ × ℝ =>
      (|(P i0).1| ^ (-(1/2) : ℝ) *
          |t * (P i0).1 + Real.sqrt (1 - t ^ 2) * (P i0).2| ^ (-(1/2) : ℝ)) *
        (|(P i1).1| ^ (-(1/2) : ℝ) *
          |t * (P i1).1 + Real.sqrt (1 - t ^ 2) * (P i1).2| ^ (-(1/2) : ℝ)))
      (Measure.pi fun _ : Fin r => ν) :=
    hprod.congr (Filter.Eventually.of_forall fun P => hprodeq P)
  refine Integrable.mono' hprod' ?_ ?_
  · -- measurability
    have hrow : Measurable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ) *
        |t * p.1 + Real.sqrt (1 - t ^ 2) * p.2| ^ (-(1/2) : ℝ)) := by
      have h1 : Measurable (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) := by
        have h : (fun p : ℝ × ℝ => |p.1| ^ (-(1/2) : ℝ)) = fun p => (Real.sqrt |p.1|)⁻¹ := by
          funext p
          rw [Real.rpow_neg (abs_nonneg _), ← Real.sqrt_eq_rpow]
        rw [h]; fun_prop
      exact h1.mul (measurable_abs_lin_rpow t (Real.sqrt (1 - t ^ 2)))
    have hm : Measurable (fun P : Fin r → ℝ × ℝ =>
        (|(P i0).1| ^ (-(1/2) : ℝ) *
            |t * (P i0).1 + Real.sqrt (1 - t ^ 2) * (P i0).2| ^ (-(1/2) : ℝ)) *
          (|(P i1).1| ^ (-(1/2) : ℝ) *
            |t * (P i1).1 + Real.sqrt (1 - t ^ 2) * (P i1).2| ^ (-(1/2) : ℝ))) :=
      (hrow.comp (measurable_pi_apply i0)).mul (hrow.comp (measurable_pi_apply i1))
    refine Measurable.aestronglyMeasurable ?_
    have hmain : Measurable (fun P : Fin r → ℝ × ℝ =>
        ((∑ i, (P i).1 ^ 2) * (∑ i, (t * (P i).1 + Real.sqrt (1 - t ^ 2) * (P i).2) ^ 2))
          ^ (-(1/2) : ℝ)) := by
      have hfun1 : Measurable (fun P : Fin r → ℝ × ℝ => ∑ i, (P i).1 ^ 2) := by fun_prop
      have hfun2 : Measurable (fun P : Fin r → ℝ × ℝ =>
          ∑ i, (t * (P i).1 + Real.sqrt (1 - t ^ 2) * (P i).2) ^ 2) := by fun_prop
      have h : (fun P : Fin r → ℝ × ℝ =>
          ((∑ i, (P i).1 ^ 2) * (∑ i, (t * (P i).1 + Real.sqrt (1 - t ^ 2) * (P i).2) ^ 2))
            ^ (-(1/2) : ℝ))
          = fun P => (Real.sqrt ((∑ i, (P i).1 ^ 2) *
              (∑ i, (t * (P i).1 + Real.sqrt (1 - t ^ 2) * (P i).2) ^ 2)))⁻¹ := by
        funext P
        rw [Real.rpow_neg (by positivity), ← Real.sqrt_eq_rpow]
      rw [h]
      exact (hfun1.mul hfun2).sqrt.inv
    exact hmain
  · filter_upwards [hx0, hx1, hy0, hy1] with P hPx0 hPx1 hPy0 hPy1
    have hx0' : (fun i => (P i).1) i0 ≠ 0 := hPx0
    have hx1' : (fun i => (P i).1) i1 ≠ 0 := hPx1
    have hy0' : (fun i => t * (P i).1 + s * (P i).2) i0 ≠ 0 := hPy0
    have hy1' : (fun i => t * (P i).1 + s * (P i).2) i1 ≠ 0 := hPy1
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by positivity) _), Real.mul_rpow
      (Finset.sum_nonneg (fun i _ => sq_nonneg ((P i).1)))
      (Finset.sum_nonneg (fun i _ => sq_nonneg (t * (P i).1 + s * (P i).2)))]
    have hxx : (∑ i, (fun i => (P i).1) i ^ 2) ^ (-(1/2) : ℝ)
        ≤ |(fun i => (P i).1) i0| ^ (-(1/2) : ℝ) * |(fun i => (P i).1) i1| ^ (-(1/2) : ℝ) :=
      inv_sqrt_sum_le_two (fun i => (P i).1) hne hx0' hx1'
    have hyy : (∑ i, (fun i => t * (P i).1 + s * (P i).2) i ^ 2) ^ (-(1/2) : ℝ)
        ≤ |(fun i => t * (P i).1 + s * (P i).2) i0| ^ (-(1/2) : ℝ) *
          |(fun i => t * (P i).1 + s * (P i).2) i1| ^ (-(1/2) : ℝ) :=
      inv_sqrt_sum_le_two (fun i => t * (P i).1 + s * (P i).2) hne hy0' hy1'
    have hnn1 : 0 ≤ (∑ i, (t * (P i).1 + s * (P i).2) ^ 2) ^ (-(1/2) : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have hnn2 : 0 ≤ |(P i0).1| ^ (-(1/2) : ℝ) * |(P i1).1| ^ (-(1/2) : ℝ) := by positivity
    calc (∑ i, (P i).1 ^ 2) ^ (-(1/2) : ℝ) *
          (∑ i, (t * (P i).1 + s * (P i).2) ^ 2) ^ (-(1/2) : ℝ)
        ≤ (|(P i0).1| ^ (-(1/2) : ℝ) * |(P i1).1| ^ (-(1/2) : ℝ)) *
            (|t * (P i0).1 + s * (P i0).2| ^ (-(1/2) : ℝ) *
              |t * (P i1).1 + s * (P i1).2| ^ (-(1/2) : ℝ)) := by
          have h1 := hxx
          have h2 := hyy
          simp only [hsdef] at h2 ⊢
          exact mul_le_mul h1 h2 hnn1 hnn2
      _ = |(P i0).1| ^ (-(1/2) : ℝ) *
            |t * (P i0).1 + Real.sqrt (1 - t ^ 2) * (P i0).2| ^ (-(1/2) : ℝ) *
            (|(P i1).1| ^ (-(1/2) : ℝ) *
              |t * (P i1).1 + Real.sqrt (1 - t ^ 2) * (P i1).2| ^ (-(1/2) : ℝ)) := by
          rw [hsdef]
          ring

end GrothendieckPair

open GrothendieckPair in
theorem solution (r : ℕ) (hr : 2 ≤ r) :
    Integrable (fun x : Fin r → ℝ => (∑ i, x i ^ 2) ^ (-(1 / 2) : ℝ))
      (Measure.pi fun _ : Fin r => gaussianReal 0 1) := GrothendieckPair.integrable_inv_norm_pi_proof r hr
