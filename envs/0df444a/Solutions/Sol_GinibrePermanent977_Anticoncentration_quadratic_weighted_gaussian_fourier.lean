-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.quadratic_weighted_gaussian_fourier
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:23:42.57225+00:00
-- url     : https://prove2.me/submissions/262b078c-d46e-47f6-a21b-78b3531a22d5

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma weighted_gaussian_pdf (q : ℝ) (hq : 0 ≤ q) (x : ℝ) :
    gaussianPDFReal 0 1 x * Real.exp (-q*x^2/2) =
      (Real.sqrt (1+q))⁻¹ * gaussianPDFReal 0 (NNReal.mk ((1+q)⁻¹) (by positivity)) x := by
  have hq' : 0 < 1+q := by linarith
  have hnorm : Real.sqrt (2*Real.pi*(1+q)⁻¹) * Real.sqrt (1+q) =
      Real.sqrt (2*Real.pi) := by
    rw [← Real.sqrt_mul (by positivity : 0 ≤ 2*Real.pi*(1+q)⁻¹)]
    congr 1
    field_simp
  have hs1 := (Real.sqrt_pos.mpr hq').ne'
  have hs2 := (Real.sqrt_pos.mpr (show 0 < 2*Real.pi*(1+q)⁻¹ by positivity)).ne'
  have hs3 := (Real.sqrt_pos.mpr (show 0 < 2*Real.pi by positivity)).ne'
  simp only [gaussianPDFReal, NNReal.coe_one, NNReal.coe_mk, mul_one, sub_zero]
  rw [mul_assoc, ← Real.exp_add]
  have he : -(x^2)/(2*1) + -q*x^2/2 = -(x^2)/(2*(1+q)⁻¹) := by field_simp; ring
  norm_num only [mul_one] at he
  rw [he]
  have hc : (Real.sqrt (2*Real.pi))⁻¹ =
      (Real.sqrt (1+q))⁻¹ * (Real.sqrt (2*Real.pi*(1+q)⁻¹))⁻¹ := by
    rw [← mul_inv, mul_comm (Real.sqrt (1+q)), hnorm]
  rw [hc]
  ring

lemma weighted_gaussian_fourier (q : ℝ) (hq : 0 ≤ q) (h : ℝ) :
    (∫ x : ℝ, (Real.exp (-q*x^2/2) : ℂ) * Complex.exp (Complex.I * (h*x : ℝ))
      ∂gaussianReal 0 1) =
    ((Real.sqrt (1+q))⁻¹ : ℂ) * Complex.exp (-(h^2 / (2*(1+q)) : ℝ)) := by
  let v : ℝ≥0 := (NNReal.mk ((1+q)⁻¹) (by positivity))
  have hv : v ≠ 0 := by apply NNReal.coe_ne_zero.mp; dsimp [v]; positivity
  have he : (∫ x : ℝ, Complex.exp (Complex.I * (h*x : ℝ)) ∂gaussianReal 0 v) =
      Complex.exp (-(h^2/(2*(1+q)) : ℝ)) := by
    have hc := charFun_gaussianReal (μ := 0) (v := v) h
    rw [charFun_apply_real] at hc
    simpa [v, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hc
  calc
    _ = ∫ x : ℝ, (gaussianPDFReal 0 1 x : ℂ) * (Real.exp (-q*x^2/2) : ℂ) *
        Complex.exp (Complex.I * (h*x : ℝ)) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      simp [Complex.real_smul, mul_assoc]
    _ = ∫ x : ℝ, ((Real.sqrt (1+q))⁻¹ : ℂ) * (gaussianPDFReal 0 v x : ℂ) *
        Complex.exp (Complex.I * (h*x : ℝ)) := by
      congr 1
      ext x
      rw [← Complex.ofReal_mul, weighted_gaussian_pdf q hq x, Complex.ofReal_mul]
      simp only [Complex.ofReal_inv, v]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, (gaussianPDFReal 0 v x : ℂ) * Complex.exp (Complex.I * (h*x : ℝ)) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, Complex.exp (Complex.I * (h*x : ℝ)) ∂gaussianReal 0 v := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      simp [Complex.real_smul]
    _ = _ := by rw [he]

lemma quadratic_in_eigenbasis {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.IsHermitian) (v : Fin d → ℝ) :
    inner ℝ (∑ i, v i • hA.eigenvectorBasis i)
      (A.toEuclideanLin (∑ i, v i • hA.eigenvectorBasis i)) =
      ∑ i, hA.eigenvalues i * (v i)^2 := by
  have heig (i : Fin d) : A.toEuclideanLin (hA.eigenvectorBasis i) =
      hA.eigenvalues i • hA.eigenvectorBasis i := by
    ext j
    exact congrFun (hA.mulVec_eigenvectorBasis i) j
  simp_rw [map_sum, map_smul, heig, smul_smul]
  have he := hA.eigenvectorBasis.orthonormal.inner_sum v
    (fun i => v i * hA.eigenvalues i) Finset.univ
  rw [he]
  apply Finset.sum_congr rfl
  intro i _
  simp only [starRingEnd_apply, star_trivial]
  ring

lemma weighted_gaussian_fourier_matrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (h : EuclideanSpace ℝ (Fin d)) :
    (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i)) : ℝ)) := by
  let q : Fin d → ℝ := hA.1.eigenvalues
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hA.1.eigenvectorBasis
  have hquad (v : Fin d → ℝ) :
      inner ℝ (∑ i, v i • b i) (A.toEuclideanLin (∑ i, v i • b i)) =
        ∑ i, q i * (v i)^2 := quadratic_in_eigenbasis A hA.1 v
  change (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+q i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (b i))^2 / (2*(1+q i)) : ℝ))

  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map (Measurable.aemeasurable (by fun_prop)) (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [hquad, inner_sum, real_inner_smul_right]
  have hfactor (v : Fin d → ℝ) :
      (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (Complex.I * (∑ i, v i * inner ℝ h (b i) : ℝ)) =
      ∏ i, (Real.exp (-q i * (v i)^2/2) : ℂ) *
        Complex.exp (Complex.I * ((inner ℝ h (b i))*v i : ℝ)) := by
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, ← Complex.exp_sum]
    congr 1
    · congr 2
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      simp only [neg_mul]
    · congr 1
      simp only [Complex.ofReal_sum, Finset.mul_sum, Complex.ofReal_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [show (∫ v : Fin d → ℝ,
        (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (Complex.I * (∑ i, v i * inner ℝ h (b i) : ℝ))
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ v : Fin d → ℝ, ∏ i,
        (Real.exp (-q i * (v i)^2/2) : ℂ) *
        Complex.exp (Complex.I * ((inner ℝ h (b i))*v i : ℝ))
          ∂Measure.pi (fun _ => gaussianReal 0 1) from
      integral_congr_ae (Filter.Eventually.of_forall hfactor)]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
    (Real.exp (-q i*x^2/2) : ℂ) * Complex.exp (Complex.I * (inner ℝ h (b i)*x : ℝ)))]
  have hw (i : Fin d) := weighted_gaussian_fourier (q i)
    (show 0 ≤ q i from hA.eigenvalues_nonneg i) (inner ℝ h (b i))
  simp_rw [hw]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  simp [Complex.ofReal_sum, Finset.sum_neg_distrib]

end GinibrePermanent977.Anticoncentration


open GinibrePermanent977.Anticoncentration

theorem solution {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (h : EuclideanSpace ℝ (Fin d)) :
    (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) *
        Complex.exp (Complex.I * (inner ℝ h y : ℝ)) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ h (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i)) : ℝ)) := by
  exact weighted_gaussian_fourier_matrix A hA h
