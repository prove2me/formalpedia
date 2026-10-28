-- Prove2me | solution 1 for KLTNuclear.Lasso.gaussian_tail
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:49:07.093433+00:00
-- url     : https://prove2.me/submissions/23ced0ae-b088-42d3-b472-fdcd81e748f8

import Mathlib
import Definitions.Def_KLTNuclear_Lasso_Model

open MeasureTheory ProbabilityTheory

namespace Aux_KLT_GT
open Filter Set

lemma hφ (y : ℝ) : gaussianPDFReal 0 1 y = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2) := by
  rw [gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]

lemma deriv_F (z : ℝ) (y : ℝ) :
    HasDerivAt (fun y : ℝ => -((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)) / z)
      (y / z * gaussianPDFReal 0 1 y) y := by
  have h1 : HasDerivAt (fun y : ℝ => -y ^ 2 / 2) (-y) y :=
    ((hasDerivAt_pow 2 y).neg.div_const 2).congr_deriv (by norm_num <;> ring)
  rw [hφ y]
  exact ((h1.exp.const_mul (Real.sqrt (2 * Real.pi))⁻¹).neg.div_const z).congr_deriv (by ring)

lemma tend_F (z : ℝ) :
    Tendsto (fun y : ℝ => -((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-y ^ 2 / 2)) / z)
      atTop (nhds 0) := by
  have h2 : Tendsto (fun y : ℝ => -y ^ 2 / 2) atTop atBot := by
    have := (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (two_ne_zero (α := ℕ)))).atBot_div_const
      (two_pos (α := ℝ))
    exact this
  have h3 : Tendsto (fun y : ℝ => Real.exp (-y ^ 2 / 2)) atTop (nhds 0) :=
    Real.tendsto_exp_atBot.comp h2
  have h4 := (h3.const_mul (Real.sqrt (2 * Real.pi))⁻¹).neg.div_const z
  rw [mul_zero, neg_zero, zero_div] at h4
  exact h4

lemma integral_tail {z : ℝ} (hz : 0 < z) :
    ∫ y in Ioi z, y / z * gaussianPDFReal 0 1 y =
      (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z := by
  have hpos : ∀ y ∈ Ioi z, 0 ≤ y / z * gaussianPDFReal 0 1 y := fun y hy =>
    mul_nonneg (div_nonneg (le_of_lt (lt_trans hz hy)) hz.le) (gaussianPDFReal_nonneg 0 1 y)
  rw [integral_Ioi_of_hasDerivAt_of_nonneg (deriv_F z z).continuousAt.continuousWithinAt
    (fun y _ => deriv_F z y) hpos (tend_F z)]
  ring

lemma integrable_tail {z : ℝ} (hz : 0 < z) :
    IntegrableOn (fun y => y / z * gaussianPDFReal 0 1 y) (Ioi z) := by
  have hpos : ∀ y ∈ Ioi z, 0 ≤ y / z * gaussianPDFReal 0 1 y := fun y hy =>
    mul_nonneg (div_nonneg (le_of_lt (lt_trans hz hy)) hz.le) (gaussianPDFReal_nonneg 0 1 y)
  exact integrableOn_Ioi_deriv_of_nonneg (deriv_F z z).continuousAt.continuousWithinAt
    (fun y _ => deriv_F z y) hpos (tend_F z)

lemma right_tail {z : ℝ} (hz : 0 < z) :
    gaussianReal 0 1 (Ioi z) ≤
      ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z) := by
  rw [gaussianReal_apply 0 one_ne_zero, gaussianPDF_def]
  have hmeas : Measurable (fun y => ENNReal.ofReal (y / z * gaussianPDFReal 0 1 y)) :=
    ((measurable_id.div_const z).mul (measurable_gaussianPDFReal 0 1)).ennreal_ofReal
  calc ∫⁻ y in Ioi z, ENNReal.ofReal (gaussianPDFReal 0 1 y)
      ≤ ∫⁻ y in Ioi z, ENNReal.ofReal (y / z * gaussianPDFReal 0 1 y) := by
        refine setLIntegral_mono hmeas (fun y hy => ENNReal.ofReal_le_ofReal ?_)
        have hy' : 1 ≤ y / z := by
          rw [le_div_iff₀ hz, one_mul]; exact le_of_lt hy
        have := gaussianPDFReal_nonneg 0 1 y
        nlinarith
    _ = ENNReal.ofReal (∫ y in Ioi z, y / z * gaussianPDFReal 0 1 y) := by
        rw [ofReal_integral_eq_lintegral_ofReal (integrable_tail hz)]
        refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun y hy => ?_))
        exact mul_nonneg (div_nonneg (le_of_lt (lt_trans hz hy)) hz.le)
          (gaussianPDFReal_nonneg 0 1 y)
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z) := by
        rw [integral_tail hz]

lemma left_eq_right (z : ℝ) : gaussianReal 0 1 (Iio (-z)) = gaussianReal 0 1 (Ioi z) := by
  have hmap : (gaussianReal 0 1).map (fun x => -x) = gaussianReal 0 1 := by
    rw [gaussianReal_map_neg]; simp
  calc gaussianReal 0 1 (Iio (-z)) = ((gaussianReal 0 1).map (fun x => -x)) (Iio (-z)) := by
        rw [hmap]
    _ = gaussianReal 0 1 ((fun x : ℝ => -x) ⁻¹' Iio (-z)) :=
        Measure.map_apply measurable_neg measurableSet_Iio
    _ = gaussianReal 0 1 (Ioi z) := by
        congr 1
        ext x
        simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_Ioi, neg_lt_neg_iff]

lemma sqrt_id : Real.sqrt (2 / Real.pi) = 2 * (Real.sqrt (2 * Real.pi))⁻¹ := by
  have h : (2 : ℝ) / Real.pi = 2 ^ 2 / (2 * Real.pi) := by ring
  rw [h, Real.sqrt_div (by positivity), Real.sqrt_sq (by norm_num), div_eq_mul_inv]

end Aux_KLT_GT

open KLTNuclear.Lasso Aux_KLT_GT in
theorem solution {z : ℝ} (hz : 0 < z) :
    gaussianReal 0 1 {y : ℝ | z < |y|} ≤
      ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-(z ^ 2) / 2) / z) := by
  have hset : {y : ℝ | z < |y|} = Set.Ioi z ∪ Set.Iio (-z) := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Ioi, Set.mem_Iio, lt_abs]
    constructor
    · rintro (h | h)
      · left; exact h
      · right; linarith
    · rintro (h | h)
      · left; exact h
      · right; linarith
  have hX0 : 0 ≤ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z := by positivity
  rw [hset]
  calc gaussianReal 0 1 (Set.Ioi z ∪ Set.Iio (-z))
      ≤ gaussianReal 0 1 (Set.Ioi z) + gaussianReal 0 1 (Set.Iio (-z)) := measure_union_le _ _
    _ ≤ ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z) +
        ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z) := by
        rw [left_eq_right z]
        exact add_le_add (right_tail hz) (right_tail hz)
    _ = ENNReal.ofReal ((Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z +
        (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-z ^ 2 / 2) / z) :=
        (ENNReal.ofReal_add hX0 hX0).symm
    _ = ENNReal.ofReal (Real.sqrt (2 / Real.pi) * Real.exp (-(z ^ 2) / 2) / z) := by
        rw [sqrt_id]
        congr 1
        ring
