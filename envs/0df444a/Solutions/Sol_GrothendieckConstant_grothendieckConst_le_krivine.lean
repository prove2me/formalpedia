-- Prove2me | solution 1 for GrothendieckConstant.grothendieckConst_le_krivine
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T23:19:48.551973+00:00
-- url     : https://prove2.me/submissions/c85a8429-0642-4db2-8539-0cf94b08f926

import Mathlib
import Definitions.Def_GrothendieckConstantDefs

set_option autoImplicit false


section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory Set Real
open scoped Topology NNReal ENNReal

namespace ImpactKrivineGaussianAngle

lemma sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)

lemma abs_sign_le (x : ℝ) : |Real.sign x| ≤ 1 := by
  rcases Real.sign_apply_eq x with h | h | h <;> simp [h]

noncomputable def angularProduct (θ t : ℝ) : ℝ :=
  Real.sign (Real.cos t) * Real.sign (Real.cos (t - θ))

lemma angularProduct_measurable (θ : ℝ) : Measurable (angularProduct θ) := by
  exact (sign_measurable.comp (by fun_prop)).mul
    (sign_measurable.comp (by fun_prop))

lemma angularProduct_integrable (θ a b : ℝ) :
    IntervalIntegrable (angularProduct θ) volume a b := by
  apply (intervalIntegrable_const (c := (1 : ℝ))).mono_fun'
    (angularProduct_measurable θ).aestronglyMeasurable
  filter_upwards with t
  simp only [angularProduct, Real.norm_eq_abs, abs_mul]
  exact mul_le_one₀ (abs_sign_le _) (abs_nonneg _) (abs_sign_le _)

lemma angularProduct_periodic (θ : ℝ) : Function.Periodic (angularProduct θ) Real.pi := by
  intro t
  dsimp [angularProduct]
  rw [show t + Real.pi - θ = (t - θ) + Real.pi by ring]
  simp [Real.cos_add_pi, Real.sign_neg]

lemma angularProduct_half_integral (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∫ t in -(Real.pi / 2)..Real.pi / 2, angularProduct θ t = Real.pi - 2 * θ := by
  have hleft : (∫ t in -(Real.pi / 2)..θ - Real.pi / 2, angularProduct θ t) = -θ := by
    calc
      _ = ∫ _t in -(Real.pi / 2)..θ - Real.pi / 2, (-1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨ht.1, by linarith [ht.2]⟩
        have hc' : Real.cos (t - θ) < 0 := by
          rw [← Real.cos_neg]
          apply Real.cos_neg_of_pi_div_two_lt_of_lt <;> linarith [ht.1, ht.2]
        simp [angularProduct, Real.sign_of_pos hc, Real.sign_of_neg hc']
      _ = -θ := by simp
  have hright : (∫ t in θ - Real.pi / 2..Real.pi / 2, angularProduct θ t) = Real.pi - θ := by
    calc
      _ = ∫ _t in θ - Real.pi / 2..Real.pi / 2, (1 : ℝ) := by
        apply intervalIntegral.integral_congr_Ioo_of_le (by linarith)
        intro t ht
        have hc : 0 < Real.cos t := Real.cos_pos_of_mem_Ioo ⟨by linarith [ht.1], ht.2⟩
        have hc' : 0 < Real.cos (t - θ) := Real.cos_pos_of_mem_Ioo
          ⟨by linarith [ht.1], by linarith [ht.2]⟩
        simp [angularProduct, Real.sign_of_pos hc, Real.sign_of_pos hc']
      _ = Real.pi - θ := by simp; ring
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (angularProduct_integrable θ (-(Real.pi / 2)) (θ - Real.pi / 2))
    (angularProduct_integrable θ (θ - Real.pi / 2) (Real.pi / 2)), hleft, hright]
  ring

lemma angularProduct_integral (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∫ t in -Real.pi..Real.pi, angularProduct θ t = 2 * Real.pi - 4 * θ := by
  have hhalf := angularProduct_half_integral θ hθ0 hθπ
  have hleft := (angularProduct_periodic θ).intervalIntegral_add_eq (-Real.pi) (-(Real.pi / 2))
  have hright := (angularProduct_periodic θ).intervalIntegral_add_eq 0 (-(Real.pi / 2))
  have he : -(Real.pi / 2) + Real.pi = Real.pi / 2 := by ring
  simp only [neg_add_cancel, zero_add, he, hhalf] at hleft hright
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (angularProduct_integrable θ (-Real.pi) 0)
    (angularProduct_integrable θ 0 Real.pi), hleft, hright]
  ring

lemma sign_mul_of_pos (r x : ℝ) (hr : 0 < r) : Real.sign (r * x) = Real.sign x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · rw [Real.sign_of_neg hx, Real.sign_of_neg (mul_neg_of_pos_of_neg hr hx)]
  · simp [hx]
  · rw [Real.sign_of_pos hx, Real.sign_of_pos (mul_pos hr hx)]

lemma radial_integral : ∫ r : ℝ in Ioi 0, r * Real.exp (-(1 / 2 : ℝ) * r ^ 2) = 1 := by
  have h := integral_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)
  have hi := (integrable_mul_cexp_neg_mul_sq (b := (1 / 2 : ℂ)) (by norm_num)).integrableOn (s := Ioi 0)
  have hr := congrArg (RCLike.re : ℂ → ℝ) h
  rw [← integral_re hi] at hr
  convert hr using 1 <;>
    norm_num [← Complex.ofReal_pow, Complex.exp_re, Complex.mul_re, Complex.mul_im]

lemma angularProduct_setIntegral (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∫ t in Ioo (-Real.pi) Real.pi, angularProduct θ t = 2 * Real.pi - 4 * θ := by
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact angularProduct_integral θ hθ0 hθπ

lemma gaussian_plane_unnormalized (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∫ p : ℝ × ℝ, Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2) *
      Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) = 2 * Real.pi - 4 * θ := by
  rw [← integral_comp_polarCoord_symm]
  calc
    _ = ∫ p : ℝ × ℝ in Ioi 0 ×ˢ Ioo (-Real.pi) Real.pi,
        (p.1 * Real.exp (-(1 / 2 : ℝ) * p.1 ^ 2)) * angularProduct θ p.2 := by
      apply setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo)
      rintro ⟨r, t⟩ ⟨hr, _⟩
      simp only [polarCoord_symm_apply, smul_eq_mul]
      have hcomb : Real.cos θ * (r * Real.cos t) + Real.sin θ * (r * Real.sin t) =
          r * Real.cos (t - θ) := by rw [Real.cos_sub]; ring
      have hsquares : (r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2 = r ^ 2 := by
        calc
          _ = r ^ 2 * (Real.cos t ^ 2 + Real.sin t ^ 2) := by ring
          _ = r ^ 2 := by rw [Real.cos_sq_add_sin_sq, mul_one]
      rw [hcomb, hsquares, sign_mul_of_pos r _ hr, sign_mul_of_pos r _ hr]
      dsimp [angularProduct]
      rw [show -(r ^ 2) / 2 = -(1 / 2 : ℝ) * r ^ 2 by ring]
      ring
    _ = (∫ r : ℝ in Ioi 0, r * Real.exp (-(1 / 2 : ℝ) * r ^ 2)) *
        ∫ t in Ioo (-Real.pi) Real.pi, angularProduct θ t :=
      by rw [← setIntegral_prod_mul]; rfl
    _ = _ := by rw [radial_integral, angularProduct_setIntegral θ hθ0 hθπ, one_mul]

lemma gaussian_density_product (x y : ℝ) :
    gaussianPDFReal 0 1 x * gaussianPDFReal 0 1 y =
      (2 * Real.pi)⁻¹ * Real.exp (-(x ^ 2 + y ^ 2) / 2) := by
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero]
  calc
    _ = ((Real.sqrt (2 * Real.pi))⁻¹ * (Real.sqrt (2 * Real.pi))⁻¹) *
        (Real.exp (-(x ^ 2) / 2) * Real.exp (-(y ^ 2) / 2)) := by ring
    _ = _ := by
      rw [← mul_inv, Real.mul_self_sqrt (show 0 ≤ 2 * Real.pi by positivity), ← Real.exp_add]
      congr 2
      ring

/-- The two-dimensional Gaussian sign correlation, including the collinear endpoints. -/
lemma gaussian_plane_sign_integral (θ : ℝ) (hθ0 : 0 ≤ θ) (hθπ : θ ≤ Real.pi) :
    ∫ p : ℝ × ℝ, Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1) = 1 - 2 * θ / Real.pi := by
  rw [gaussianReal_of_var_ne_zero 0 (by norm_num : (1 : ℝ≥0) ≠ 0),
    prod_withDensity (measurable_gaussianPDF 0 1) (measurable_gaussianPDF 0 1)]
  rw [integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (Filter.Eventually.of_forall fun _ => ENNReal.mul_lt_top gaussianPDF_lt_top gaussianPDF_lt_top)]
  simp only [ENNReal.toReal_mul, toReal_gaussianPDF, smul_eq_mul]
  calc
    _ = (2 * Real.pi)⁻¹ * ∫ p : ℝ × ℝ,
        Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2) *
          Real.exp (-(p.1 ^ 2 + p.2 ^ 2) / 2) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with p
      rw [gaussian_density_product]
      ring
    _ = _ := by
      rw [gaussian_plane_unnormalized θ hθ0 hθπ]
      field_simp
      ring

end ImpactKrivineGaussianAngle
end


section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace Topology

namespace ImpactKrivineGaussianTransport

lemma sign_measurable : Measurable Real.sign := by
  unfold Real.sign
  exact Measurable.ite (measurableSet_lt measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_lt measurable_const measurable_id) measurable_const measurable_const)

lemma dual_pair (L : StrongDual ℝ (ℝ × ℝ)) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have h : (x, y) = x • (1, 0) + y • (0, 1) := by ext <;> simp
  rw [h, map_add, map_smul, map_smul]
  rfl

lemma charFunDual_standard_real (L : StrongDual ℝ ℝ) :
    charFunDual (gaussianReal 0 1) L = Complex.exp (- (L 1 : ℂ) ^ 2 / 2) := by
  have h : charFunDual (gaussianReal 0 1) L = charFun (gaussianReal 0 1) (L 1) := by
    rw [charFunDual_apply, charFun_apply_real]
    congr 1
    ext x
    have hx : L x = x * L 1 := by
      simpa using L.map_smul x (1 : ℝ)
    rw [hx]
    push_cast
    ring_nf
  rw [h, charFun_gaussianReal]
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, NNReal.coe_one, Complex.ofReal_one,
    one_mul, zero_sub]
  congr 1
  ring

noncomputable def projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    EuclideanSpace ℝ (Fin d) →L[ℝ] (ℝ × ℝ) :=
  (innerSL ℝ u).prod (innerSL ℝ v)

noncomputable def planePair (θ : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (ContinuousLinearMap.fst ℝ ℝ ℝ).prod
    (Real.cos θ • ContinuousLinearMap.fst ℝ ℝ ℝ +
      Real.sin θ • ContinuousLinearMap.snd ℝ ℝ ℝ)

lemma dual_projectionPair {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (L : StrongDual ℝ (ℝ × ℝ)) :
    L.comp (projectionPair u v) = innerSL ℝ (L (1, 0) • u + L (0, 1) • v) := by
  ext g
  simp only [ContinuousLinearMap.comp_apply, projectionPair, ContinuousLinearMap.prod_apply,
    innerSL_apply_apply, inner_add_left, real_inner_smul_left]
  rw [dual_pair]
  ring

lemma norm_combination_sq {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (t s : ℝ) :
    ‖t • u + s • v‖ ^ 2 = t ^ 2 + s ^ 2 + 2 * t * s * inner ℝ u v := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, hu, hv, real_inner_comm v u]
  ring

/-- Equality of the joint projection laws, including singular Gram matrices. -/
theorem projectionPair_law {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : Real.cos θ = inner ℝ u v) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (projectionPair u v) =
      ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (planePair θ) := by
  apply Measure.ext_of_charFunDual
  ext L
  rw [charFunDual_map, charFunDual_map, dual_projectionPair, charFunDual_stdGaussian,
    innerSL_apply_norm, charFunDual_prod, charFunDual_standard_real,
    charFunDual_standard_real, ← Complex.exp_add]
  have hleft : (L.comp (planePair θ)).comp (ContinuousLinearMap.inl ℝ ℝ ℝ) 1 =
      L (1, 0) + Real.cos θ * L (0, 1) := by
    change L (1, Real.cos θ * 1 + Real.sin θ * 0) = _
    rw [dual_pair]
    simp
  have hright : (L.comp (planePair θ)).comp (ContinuousLinearMap.inr ℝ ℝ ℝ) 1 =
      Real.sin θ * L (0, 1) := by
    change L (0, Real.cos θ * 0 + Real.sin θ * 1) = _
    rw [dual_pair]
    simp
  rw [hleft, hright]
  have hnorm := norm_combination_sq u v hu hv (L (1, 0)) (L (0, 1))
  have hgram : ‖L (1, 0) • u + L (0, 1) • v‖ ^ 2 =
      (L (1, 0) + Real.cos θ * L (0, 1)) ^ 2 + (Real.sin θ * L (0, 1)) ^ 2 := by
    rw [hnorm, ← hθ]
    nlinarith [Real.sin_sq_add_cos_sq θ]
  congr 1
  have hc := congrArg (fun x : ℝ => (x : ℂ)) hgram
  push_cast at hc ⊢
  linear_combination -hc / 2

/-- Transport of the sign correlation from the plane to unit vectors. -/
theorem sign_integral_transport {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (θ : ℝ) (hθ : Real.cos θ = inner ℝ u v) :
    (∫ g, Real.sign (inner ℝ g u) * Real.sign (inner ℝ g v)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
    ∫ p : ℝ × ℝ, Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let f : ℝ × ℝ → ℝ := fun p => Real.sign p.1 * Real.sign p.2
  have hf : Measurable f :=
    (sign_measurable.comp measurable_fst).mul (sign_measurable.comp measurable_snd)
  have h := congrArg (fun μ : Measure (ℝ × ℝ) => ∫ p, f p ∂μ)
    (projectionPair_law u v hu hv θ hθ)
  rw [integral_map (projectionPair u v).continuous.measurable.aemeasurable
      hf.aestronglyMeasurable,
    integral_map (planePair θ).continuous.measurable.aemeasurable
      hf.aestronglyMeasurable] at h
  change (∫ g, Real.sign (inner ℝ u g) * Real.sign (inner ℝ v g)
    ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
    (∫ p : ℝ × ℝ, Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2)
      ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) at h
  simpa only [real_inner_comm u, real_inner_comm v] using h

/-- Conditional Gaussian arcsine identity. The planar identity is the sole mathematical input. -/
theorem gaussian_sign_arcsine_of_planar
    (planar : ∀ θ : ℝ, 0 ≤ θ → θ ≤ Real.pi →
      (∫ p : ℝ × ℝ, Real.sign p.1 * Real.sign (Real.cos θ * p.1 + Real.sin θ * p.2)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) = 1 - 2 * θ / Real.pi)
    (d : ℕ) (u v : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ g, Real.sign (inner ℝ g u) * Real.sign (inner ℝ g v)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (2 / Real.pi) * Real.arcsin (inner ℝ u v) := by
  have hρ : |inner ℝ u v| ≤ 1 := by
    simpa [hu, hv] using abs_real_inner_le_norm u v
  rw [sign_integral_transport u v hu hv (Real.arccos (inner ℝ u v))
    (Real.cos_arccos (abs_le.mp hρ).1 (abs_le.mp hρ).2)]
  rw [planar _ (Real.arccos_nonneg _) (Real.arccos_le_pi _),
    Real.arcsin_eq_pi_div_two_sub_arccos]
  field_simp


end ImpactKrivineGaussianTransport
end


section
set_option autoImplicit false

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace NNReal ENNReal

namespace ImpactKrivineGaussianBridge

lemma unit_projection_law {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    (stdGaussian (EuclideanSpace ℝ (Fin d))).map (fun x => inner ℝ x u) = gaussianReal 0 1 := by
  let L : StrongDual ℝ (EuclideanSpace ℝ (Fin d)) := innerSL ℝ u
  have hL : ‖L‖ = 1 := by simp [L, hu]
  have hm : (stdGaussian (EuclideanSpace ℝ (Fin d))).map L = gaussianReal 0 1 := by
    rw [IsGaussian.map_eq_gaussianReal, integral_strongDual_stdGaussian,
      variance_dual_stdGaussian, hL]
    norm_num
  convert hm using 1
  congr 1
  ext x
  simpa [L] using (real_inner_comm x u).symm

lemma unit_projection_ne_zero_ae {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) (hu : ‖u‖ = 1) :
    ∀ᵐ x ∂stdGaussian (EuclideanSpace ℝ (Fin d)), inner ℝ x u ≠ 0 := by
  let _ := nullSingletonClass_gaussianReal (μ := (0 : ℝ)) (by norm_num : (1 : ℝ≥0) ≠ 0)
  have hn : ∀ᵐ t : ℝ ∂gaussianReal 0 1, t ≠ 0 := (gaussianReal 0 1).ae_ne 0
  rw [← unit_projection_law u hu] at hn
  exact ae_of_ae_map (f := fun x : EuclideanSpace ℝ (Fin d) => inner ℝ x u)
    (p := fun t : ℝ => t ≠ 0) (by fun_prop) hn

lemma sign_eq_rounding {x : ℝ} (hx : x ≠ 0) :
    Real.sign x = if 0 ≤ x then (1 : ℝ) else -1 := by
  by_cases h : 0 ≤ x
  · rw [if_pos h, Real.sign_of_pos (lt_of_le_of_ne h (Ne.symm hx))]
  · rw [if_neg h, Real.sign_of_neg (lt_of_not_ge h)]

lemma integral_rounding_eq_sign {d : ℕ} (u v : EuclideanSpace ℝ (Fin d))
    (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    (∫ x, (if 0 ≤ inner ℝ x u then (1 : ℝ) else -1) *
      (if 0 ≤ inner ℝ x v then (1 : ℝ) else -1) ∂stdGaussian _) =
    ∫ x, Real.sign (inner ℝ x u) * Real.sign (inner ℝ x v) ∂stdGaussian _ := by
  apply integral_congr_ae
  filter_upwards [unit_projection_ne_zero_ae u hu, unit_projection_ne_zero_ae v hv] with x hx hy
  rw [sign_eq_rounding hx, sign_eq_rounding hy]

end ImpactKrivineGaussianBridge
end


section
set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators Matrix
open Filter Matrix

namespace ImpactKrivineAlgebra

noncomputable def c : ℝ := Real.log (1 + Real.sqrt 2)

lemma c_pos : 0 < c := Real.log_pos (by have := Real.sqrt_pos.2 (show (0:ℝ) < 2 by norm_num); linarith)

lemma sinh_c : Real.sinh c = 1 := by
  convert Real.sinh_arsinh 1 using 1; norm_num [Real.arsinh, c]

lemma c_lt_pi_half : c < Real.pi / 2 := by
  have h := Real.log_lt_sub_one_of_pos (show (0:ℝ) < 1 + Real.sqrt 2 by positivity)
    (show (1:ℝ) + Real.sqrt 2 ≠ 1 by have := Real.sqrt_pos.2 (show (0:ℝ) < 2 by norm_num); linarith)
  have hs := Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num)
  have hp := Real.pi_gt_three
  dsimp [c]
  nlinarith [Real.sqrt_nonneg (2:ℝ)]

lemma arcsin_sin_c_mul {t : ℝ} (ht : |t| ≤ 1) :
    Real.arcsin (Real.sin (c * t)) = c * t := by
  apply Real.arcsin_sin
  · have := (abs_le.mp ht).1; nlinarith [c_pos, c_lt_pi_half]
  · have := (abs_le.mp ht).2; nlinarith [c_pos, c_lt_pi_half]

variable {ι : Type*} [Fintype ι]

lemma psd_entrywise_pow (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (k : ℕ) :
    Matrix.PosSemidef (fun i j => G i j ^ k) := by
  induction k with
  | zero =>
    have he : (fun i j => G i j ^ 0 : Matrix ι ι ℝ) =
        Matrix.vecMulVec (fun _ : ι => (1:ℝ)) (star (fun _ : ι => (1:ℝ))) := by
      ext i j; simp [Matrix.vecMulVec]
    rw [he]
    exact Matrix.posSemidef_vecMulVec_self_star _
  | succ k hk =>
    have he : (fun i j => G i j ^ (k+1) : Matrix ι ι ℝ) =
        (fun i j => G i j ^ k) ⊙ G := by
      ext i j; simp [pow_succ, Matrix.hadamard]
    rw [he]
    exact hk.hadamard hG

/-- Signed odd-power terms implement the two blocks by a diagonal congruence. -/
noncomputable def term (G : Matrix ι ι ℝ) (side : ι → Bool) (k : ℕ) : Matrix ι ι ℝ :=
  fun i j => (c ^ (2*k+1) / (2*k+1).factorial) *
    ((if side i then (-1:ℝ)^k else 1) * (if side j then (-1:ℝ)^k else 1) * G i j ^ (2*k+1))

lemma term_psd (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (side : ι → Bool) (k : ℕ) :
    (term G side k).PosSemidef := by
  have h := (Matrix.posSemidef_vecMulVec_self_star
    (fun i => if side i then (-1:ℝ)^k else 1)).hadamard (psd_entrywise_pow G hG (2*k+1))
  have he : term G side k = (c ^ (2*k+1) / ((2*k+1).factorial:ℝ)) •
      ((Matrix.vecMulVec (fun i => if side i then (-1:ℝ)^k else 1)
        (star (fun i => if side i then (-1:ℝ)^k else 1))) ⊙
        (fun i j => G i j ^ (2*k+1))) := by
    ext i j
    simp only [term, Matrix.smul_apply, smul_eq_mul, Matrix.hadamard, Matrix.of_apply,
      Matrix.vecMulVec_apply, star_trivial]
  rw [he]
  exact h.smul (div_nonneg (pow_nonneg c_pos.le _) (Nat.cast_nonneg _))

noncomputable def transform (G : Matrix ι ι ℝ) (side : ι → Bool) : Matrix ι ι ℝ :=
  fun i j => if side i = side j then Real.sinh (c * G i j) else Real.sin (c * G i j)

omit [Fintype ι] in
lemma term_hasSum (G : Matrix ι ι ℝ) (side : ι → Bool) (i j : ι) :
    HasSum (fun k => term G side k i j) (transform G side i j) := by
  cases hi : side i <;> cases hj : side j
  · simpa [term, transform, hi, hj, mul_pow, div_mul_eq_mul_div] using Real.hasSum_sinh (c * G i j)
  · convert Real.hasSum_sin (c * G i j) using 1
    · ext k; simp [term, hi, hj, mul_pow]; ring
    · simp [transform, hi, hj]
  · convert Real.hasSum_sin (c * G i j) using 1
    · ext k; simp [term, hi, hj, mul_pow]; ring
    · simp [transform, hi, hj]
  · convert Real.hasSum_sinh (c * G i j) using 1
    · ext k
      simp only [term, hi, hj, ↓reduceIte]
      rw [← mul_pow]
      norm_num
      simp only [mul_pow]
      ring
    · simp [transform, hi, hj]

lemma psd_limit {M : ℕ → Matrix ι ι ℝ} {B : Matrix ι ι ℝ}
    (hM : ∀ k, (M k).PosSemidef) (hlim : ∀ i j, Tendsto (fun k => M k i j) atTop (nhds (B i j))) :
    B.PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
  · ext i j
    simp only [Matrix.conjTranspose_apply, star_trivial]
    exact tendsto_nhds_unique (hlim j i) ((hlim i j).congr (fun k => by
      have h := congrFun (congrFun (hM k).isHermitian i) j
      simpa using h.symm))
  · intro x
    have hlimq : Tendsto (fun k => star x ⬝ᵥ (M k *ᵥ x)) atTop
        (nhds (star x ⬝ᵥ (B *ᵥ x))) := by
      simp only [dotProduct, mulVec]
      exact tendsto_finsetSum _ fun i _ => tendsto_const_nhds.mul
        (tendsto_finsetSum _ fun j _ => (hlim i j).mul_const (x j))
    exact ge_of_tendsto hlimq (Filter.Eventually.of_forall fun k => (hM k).dotProduct_mulVec_nonneg x)

lemma transform_psd (G : Matrix ι ι ℝ) (hG : G.PosSemidef) (side : ι → Bool) :
    (transform G side).PosSemidef := by
  apply psd_limit (M := fun n => ∑ k ∈ Finset.range n, term G side k)
  · intro n
    induction n with
    | zero => simpa using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
    | succ n hn => simpa [Finset.sum_range_succ] using hn.add (term_psd G hG side n)
  · intro i j
    simpa only [Matrix.sum_apply] using (term_hasSum G side i j).tendsto_sum_nat

omit [Fintype ι] in
lemma transform_diag (G : Matrix ι ι ℝ) (side : ι → Bool) (hdiag : ∀ i, G i i = 1) (i : ι) :
    transform G side i i = 1 := by simp [transform, hdiag, sinh_c]

section Factorization
open scoped MatrixOrder

/-- Columns of the positive square root realize any finite real PSD matrix. -/
lemma exists_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) :
    ∃ w : ι → EuclideanSpace ℝ ι, ∀ i j, inner ℝ (w i) (w j) = B i j := by
  classical
  let R := CFC.sqrt B
  have hR : R.IsHermitian := (CFC.sqrt_nonneg B).posSemidef.isHermitian
  have hsq : R * R = B := CFC.sqrt_mul_sqrt_self B hB.nonneg
  refine ⟨fun i => WithLp.toLp 2 (R.transpose i), ?_⟩
  intro i j
  rw [inner_matrix_col_col, hR, hsq]

end Factorization

lemma exists_unit_gram (B : Matrix ι ι ℝ) (hB : B.PosSemidef) (hdiag : ∀ i, B i i = 1) :
    ∃ w : ι → EuclideanSpace ℝ (Fin (Fintype.card ι)),
      (∀ i, ‖w i‖ = 1) ∧ (∀ i j, inner ℝ (w i) (w j) = B i j) := by
  classical
  obtain ⟨w, hw⟩ := exists_gram B hB
  let e := LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (Fintype.equivFin ι)
  refine ⟨fun i => e (w i), ?_, ?_⟩
  · intro i
    rw [e.norm_map]
    have h := hw i i
    rw [real_inner_self_eq_norm_sq, hdiag] at h
    nlinarith [norm_nonneg (w i)]
  · intro i j
    rw [e.inner_map_map, hw]

/-- Finite-dimensional Krivine preprocessing, including degenerate empty families. -/
lemma preprocess {m n d : ℕ}
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    ∃ D : ℕ, ∃ U : Fin m → EuclideanSpace ℝ (Fin D),
      ∃ V : Fin n → EuclideanSpace ℝ (Fin D),
      (∀ i, ‖U i‖ = 1) ∧ (∀ j, ‖V j‖ = 1) ∧
      (∀ i j, inner ℝ (U i) (V j) = Real.sin (c * inner ℝ (u i) (v j))) := by
  let w := Sum.elim u v
  let G := Matrix.gram ℝ w
  let side : Fin m ⊕ Fin n → Bool := Sum.elim (fun _ => false) (fun _ => true)
  have hG : G.PosSemidef := Matrix.posSemidef_gram ℝ w
  have hdiag : ∀ i, G i i = 1 := by
    intro i
    cases i with
    | inl i => simp [G, w, Matrix.gram_apply, hu]
    | inr j => simp [G, w, Matrix.gram_apply, hv]
  obtain ⟨z, hz, hzgram⟩ := exists_unit_gram (transform G side)
    (transform_psd G hG side) (transform_diag G side hdiag)
  refine ⟨Fintype.card (Fin m ⊕ Fin n), fun i => z (.inl i), fun j => z (.inr j),
    (fun i => hz _), (fun j => hz _), ?_⟩
  intro i j
  simpa [transform, G, w, side, Matrix.gram_apply] using hzgram (.inl i) (.inr j)


open GrothendieckConstant MeasureTheory ProbabilityTheory

/- The elementary objective bounds and the one-dimensional test below are copied
from Solutions/ImpactGrothPiLower.lean, SHA256 24dde010041a637b44927712c821efa295c10f551f5d6ebe927666cd60aeaeaf.
The objective bounds originate in Nickrobbins95, Prove2Me submission
f260128e-39ad-469d-96d6-7bf32941862c. No dependency on the lower-bound theorem is used. -/

theorem optSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (optSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨x, y, hx, hy, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 := le_abs_self (A i j)
  have h2 := neg_abs_le (A i j)
  rcases hx i with h | h <;> rcases hy j with h' | h' <;> rw [h, h'] <;> linarith


theorem sdpSet_bdd {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : BddAbove (sdpSet A) := by
  refine ⟨∑ i, ∑ j, |A i j|, ?_⟩
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro j _
  have h1 : |inner ℝ (u i) (v j)| ≤ 1 := by
    have := abs_real_inner_le_norm (u i) (v j)
    rw [hu i, hv j] at this
    simpa using this
  calc A i j * inner ℝ (u i) (v j) ≤ |A i j * inner ℝ (u i) (v j)| := le_abs_self _
    _ = |A i j| * |inner ℝ (u i) (v j)| := abs_mul _ _
    _ ≤ |A i j| * 1 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |A i j| := mul_one _


theorem one_le_of_isGrothendieckBound {K : ℝ} (hK : IsGrothendieckBound K) : 1 ≤ K := by
  let A : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => 1
  have hmem : (1 : ℝ) ∈ optSet A := by
    refine ⟨fun _ => 1, fun _ => 1, fun _ => Or.inl rfl, fun _ => Or.inl rfl, ?_⟩
    simp [A]
  have hopt : optValue A = 1 := by
    apply le_antisymm
    · apply csSup_le ⟨1, hmem⟩
      rintro s ⟨x, y, hx, hy, rfl⟩
      simp only [A, Fin.sum_univ_one, one_mul]
      rcases hx 0 with h | h <;> rcases hy 0 with h' | h' <;> rw [h, h'] <;> norm_num
    · exact le_csSup (optSet_bdd A) hmem
  let v : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have hv : ‖v‖ = 1 := by simp [v, EuclideanSpace.norm_eq]
  have hsdp : 1 ≤ sdpValue A := by
    apply le_csSup (sdpSet_bdd A)
    refine ⟨1, fun _ => v, fun _ => v, fun _ => hv, fun _ => hv, ?_⟩
    simp [A, hv]
  have h := hK 1 1 A
  rw [hopt, mul_one] at h
  exact hsdp.trans h


lemma sdpSet_nonempty {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : (sdpSet A).Nonempty := by
  let e : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ => 1)
  have he : ‖e‖ = 1 := by simp [e, EuclideanSpace.norm_eq]
  exact ⟨_, 1, (fun _ => e), (fun _ => e), (fun _ => he), (fun _ => he), rfl⟩

/-- Hyperplane sign with the positive convention on its zero set. -/
noncomputable def roundingSign {d : ℕ} (u g : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if 0 ≤ inner ℝ g u then 1 else -1

lemma roundingSign_pm {d : ℕ} (u g : EuclideanSpace ℝ (Fin d)) :
    roundingSign u g = 1 ∨ roundingSign u g = -1 := by
  unfold roundingSign; split_ifs <;> simp

lemma roundingSign_measurable {d : ℕ} (u : EuclideanSpace ℝ (Fin d)) :
    Measurable (roundingSign u) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact isClosed_le continuous_const (by fun_prop) |>.measurableSet

lemma roundingSign_product_integrable {d : ℕ} (u v : EuclideanSpace ℝ (Fin d)) :
    Integrable (fun g => roundingSign u g * roundingSign v g)
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
  apply (integrable_const (1:ℝ)).mono'
    ((roundingSign_measurable u).mul (roundingSign_measurable v)).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro g
  rcases roundingSign_pm u g with hu | hu <;>
    rcases roundingSign_pm v g with hv | hv <;> simp [hu, hv]

/-- Gaussian hyperplane correlation used by the finite rounding argument. -/
def GaussianSignCorrelation : Prop :=
  ∀ (d : ℕ) (u v : EuclideanSpace ℝ (Fin d)), ‖u‖ = 1 → ‖v‖ = 1 →
    (∫ g, roundingSign u g * roundingSign v g ∂stdGaussian (EuclideanSpace ℝ (Fin d))) =
      (2 / Real.pi) * Real.arcsin (inner ℝ u v)

lemma rounded_objective_le_opt {m n d : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (U : Fin m → EuclideanSpace ℝ (Fin d)) (V : Fin n → EuclideanSpace ℝ (Fin d)) :
    (∫ g, ∑ i, ∑ j, A i j * (roundingSign (U i) g * roundingSign (V j) g)
      ∂stdGaussian (EuclideanSpace ℝ (Fin d))) ≤ optValue A := by
  have hpoint (g : EuclideanSpace ℝ (Fin d)) :
      (∑ i, ∑ j, A i j * (roundingSign (U i) g * roundingSign (V j) g)) ≤ optValue A := by
    apply le_csSup (optSet_bdd A)
    refine ⟨fun i => roundingSign (U i) g, fun j => roundingSign (V j) g,
      fun i => roundingSign_pm _ _, fun j => roundingSign_pm _ _, ?_⟩
    simp only [mul_assoc]
  have hint : Integrable (fun g => ∑ i, ∑ j,
      A i j * (roundingSign (U i) g * roundingSign (V j) g))
      (stdGaussian (EuclideanSpace ℝ (Fin d))) := by
    apply integrable_finsetSum; intro i _
    apply integrable_finsetSum; intro j _
    exact (roundingSign_product_integrable _ _).const_mul _
  simpa using integral_mono hint (integrable_const (optValue A)) hpoint

lemma objective_le_krivine_opt (hgauss : GaussianSignCorrelation) {m n d : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (u : Fin m → EuclideanSpace ℝ (Fin d)) (v : Fin n → EuclideanSpace ℝ (Fin d))
    (hu : ∀ i, ‖u i‖ = 1) (hv : ∀ j, ‖v j‖ = 1) :
    (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) ≤
      (Real.pi / (2*c)) * optValue A := by
  obtain ⟨D, U, V, hU, hV, hcross⟩ := preprocess u v hu hv
  have hcor (i : Fin m) (j : Fin n) :
      (∫ g, roundingSign (U i) g * roundingSign (V j) g
        ∂stdGaussian (EuclideanSpace ℝ (Fin D))) =
          (2*c/Real.pi) * inner ℝ (u i) (v j) := by
    rw [hgauss D _ _ (hU i) (hV j), hcross]
    have habs : |inner ℝ (u i) (v j)| ≤ 1 := by
      simpa [hu, hv] using abs_real_inner_le_norm (u i) (v j)
    rw [arcsin_sin_c_mul habs]
    ring
  have hint (i : Fin m) (j : Fin n) : Integrable
      (fun g => A i j * (roundingSign (U i) g * roundingSign (V j) g))
      (stdGaussian (EuclideanSpace ℝ (Fin D))) :=
    (roundingSign_product_integrable _ _).const_mul _
  have heq : (∫ g, ∑ i, ∑ j, A i j * (roundingSign (U i) g * roundingSign (V j) g)
      ∂stdGaussian (EuclideanSpace ℝ (Fin D))) =
      (2*c/Real.pi) * (∑ i, ∑ j, A i j * inner ℝ (u i) (v j)) := by
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hint i j))]
    simp_rw [integral_finsetSum _ (fun j _ => hint _ j), integral_const_mul, hcor]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  have h := rounded_objective_le_opt A U V
  rw [heq] at h
  have hc : 0 < 2*c/Real.pi := div_pos (mul_pos (by norm_num) c_pos) Real.pi_pos
  have hr : Real.pi / (2*c) = (2*c/Real.pi)⁻¹ := by field_simp
  rw [hr]
  exact (le_inv_mul_iff₀ hc).2 h

lemma isGrothendieckBound_of_gaussianSignCorrelation (hgauss : GaussianSignCorrelation) :
    IsGrothendieckBound (Real.pi / (2*c)) := by
  intro m n A
  apply csSup_le (sdpSet_nonempty A)
  rintro s ⟨d, u, v, hu, hv, rfl⟩
  exact objective_le_krivine_opt hgauss A u v hu hv

/-- Complete conditional reduction of the canonical target to Gaussian sign correlation. -/
theorem krivine_upper_of_gaussianSignCorrelation (hgauss : GaussianSignCorrelation) :
    grothendieckConst ≤ Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
  apply csInf_le
  · exact ⟨1, fun K hK => one_le_of_isGrothendieckBound hK⟩
  · exact isGrothendieckBound_of_gaussianSignCorrelation hgauss

end ImpactKrivineAlgebra
end


/-- Krivine's classical upper bound from Gaussian rounding and finite PSD preprocessing. -/
theorem solution : GrothendieckConstant.grothendieckConst ≤
    Real.pi / (2 * Real.log (1 + Real.sqrt 2)) := by
  apply ImpactKrivineAlgebra.krivine_upper_of_gaussianSignCorrelation
  intro d u v hu hv
  change (∫ x, (if 0 ≤ inner ℝ x u then (1 : ℝ) else -1) *
    (if 0 ≤ inner ℝ x v then (1 : ℝ) else -1)
    ∂ProbabilityTheory.stdGaussian (EuclideanSpace ℝ (Fin d))) = _
  rw [ImpactKrivineGaussianBridge.integral_rounding_eq_sign u v hu hv]
  exact ImpactKrivineGaussianTransport.gaussian_sign_arcsine_of_planar
    ImpactKrivineGaussianAngle.gaussian_plane_sign_integral d u v hu hv
