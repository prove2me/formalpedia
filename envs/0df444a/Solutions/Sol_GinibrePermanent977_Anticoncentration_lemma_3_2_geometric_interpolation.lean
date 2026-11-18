-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.lemma_3_2_geometric_interpolation
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:31:37.911862+00:00
-- url     : https://prove2.me/submissions/c264a199-2578-411c-b006-f653211310b6

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model
import Theorems.Thm_GinibrePermanent977_Anticoncentration_quadratic_weighted_gaussian_fourier
import Theorems.Thm_GinibrePermanent977_Anticoncentration_lemma_3_1_quadratic_scaling

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


open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma weighted_gaussian_mgf (q : ℝ) (hq : 0 ≤ q) (z : ℂ) :
    (∫ x : ℝ, (Real.exp (-q*x^2/2) : ℂ) * Complex.exp (z * (x : ℂ))
      ∂gaussianReal 0 1) =
    ((Real.sqrt (1+q))⁻¹ : ℂ) * Complex.exp (z^2 / (2*(1+q) : ℝ)) := by
  let v : ℝ≥0 := (NNReal.mk ((1+q)⁻¹) (by positivity))
  have hv : v ≠ 0 := by apply NNReal.coe_ne_zero.mp; dsimp [v]; positivity
  have he : (∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂gaussianReal 0 v) =
      Complex.exp (z^2 / (2*(1+q) : ℝ)) := by
    have hc := complexMGF_id_gaussianReal (μ := 0) (v := v) z
    simpa [complexMGF, v, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv] using hc

  calc
    _ = ∫ x : ℝ, (gaussianPDFReal 0 1 x : ℂ) * (Real.exp (-q*x^2/2) : ℂ) *
        Complex.exp (z * (x : ℂ)) := by
      rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1 : ℝ≥0) ≠ 0)]
      simp [Complex.real_smul, mul_assoc]
    _ = ∫ x : ℝ, ((Real.sqrt (1+q))⁻¹ : ℂ) * (gaussianPDFReal 0 v x : ℂ) *
        Complex.exp (z * (x : ℂ)) := by
      congr 1
      ext x
      rw [← Complex.ofReal_mul, weighted_gaussian_pdf q hq x, Complex.ofReal_mul]
      simp only [Complex.ofReal_inv, v]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, (gaussianPDFReal 0 v x : ℂ) * Complex.exp (z * (x : ℂ)) := by
      simp_rw [mul_assoc]
      rw [integral_const_mul]
    _ = ((Real.sqrt (1+q))⁻¹ : ℂ) *
        ∫ x : ℝ, Complex.exp (z * (x : ℂ)) ∂gaussianReal 0 v := by
      rw [integral_gaussianReal_eq_integral_smul hv]
      simp [Complex.real_smul]
    _ = _ := by rw [he]

lemma weighted_gaussian_mgf_matrix {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (l : EuclideanSpace ℝ (Fin d) →ₗ[ℝ] ℂ) :
    (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) * Complex.exp (l y) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (∑ i, (l (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i) : ℝ)) := by
  let q : Fin d → ℝ := hA.1.eigenvalues
  let b : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hA.1.eigenvectorBasis
  have hquad (v : Fin d → ℝ) :
      inner ℝ (∑ i, v i • b i) (A.toEuclideanLin (∑ i, v i • b i)) =
        ∑ i, q i * (v i)^2 := quadratic_in_eigenbasis A hA.1 v
  change (∫ y : EuclideanSpace ℝ (Fin d),
      (Real.exp (-inner ℝ y (A.toEuclideanLin y)/2) : ℂ) * Complex.exp (l y) ∂stdGaussian _) =
      (∏ i, ((Real.sqrt (1+q i))⁻¹ : ℂ)) *
        Complex.exp (∑ i, (l (b i))^2 / (2*(1+q i) : ℝ))
  rw [stdGaussian_eq_map_pi_orthonormalBasis b]
  rw [integral_map (Measurable.aemeasurable (by fun_prop))
    (Measurable.aestronglyMeasurable (by fun_prop))]
  simp_rw [hquad, map_sum, map_smul, Complex.real_smul]
  have hfactor (v : Fin d → ℝ) :
      (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (∑ i, (v i : ℂ) * l (b i)) =
      ∏ i, (Real.exp (-q i * (v i)^2/2) : ℂ) * Complex.exp (l (b i)*(v i : ℂ)) := by
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod, ← Real.exp_sum, ← Complex.exp_sum]
    congr 1
    · congr 2
      rw [← Finset.sum_neg_distrib, Finset.sum_div]
      simp only [neg_mul]
    · congr 1
      apply Finset.sum_congr rfl
      intro i _
      ring
  rw [show (∫ v : Fin d → ℝ,
        (Real.exp (-(∑ i, q i * v i ^2)/2) : ℂ) *
          Complex.exp (∑ i, (v i : ℂ)*l (b i))
          ∂Measure.pi (fun _ => gaussianReal 0 1)) =
      ∫ v : Fin d → ℝ, ∏ i,
        (Real.exp (-q i * (v i)^2/2) : ℂ) * Complex.exp (l (b i)*(v i : ℂ))
          ∂Measure.pi (fun _ => gaussianReal 0 1) from
      integral_congr_ae (Filter.Eventually.of_forall hfactor)]
  rw [integral_fintype_prod_eq_prod (fun i (x : ℝ) =>
    (Real.exp (-q i*x^2/2) : ℂ) * Complex.exp (l (b i)*(x : ℂ)))]
  have hw (i : Fin d) := weighted_gaussian_mgf (q i)
    (show 0 ≤ q i from hA.eigenvalues_nonneg i) (l (b i))
  simp_rw [hw]
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]

lemma weighted_gaussian_mgf_raw {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (l : (Fin d → ℝ) →ₗ[ℝ] ℂ) :
    (∫ y : Fin d → ℝ, (Real.exp (-(y ⬝ᵥ (A *ᵥ y))/2) : ℂ) *
        Complex.exp (l y) ∂SmoothBerr.stdGaussianVec d) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (∑ i, (l (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i) : ℝ)) := by
  have hc := weighted_gaussian_mgf_matrix A hA
    (l.comp (WithLp.linearEquiv 2 ℝ (Fin d → ℝ)).toLinearMap)
  rw [← map_pi_eq_stdGaussian,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))] at hc
  simpa [SmoothBerr.stdGaussianVec, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toLpLin_apply, dotProduct_comm] using hc

end GinibrePermanent977.Anticoncentration


open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma gaussian_dot_characteristic {d : ℕ} (v : Fin d → ℝ) :
    (∫ x : Fin d → ℝ, Complex.exp (Complex.I * (x ⬝ᵥ v : ℝ))
      ∂SmoothBerr.stdGaussianVec d) = (Real.exp (-(∑ i, v i^2)/2) : ℂ) := by
  have hc := charFun_stdGaussian (WithLp.toLp 2 v)
  rw [← map_pi_eq_stdGaussian, charFun_apply,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))] at hc
  simp only [← Complex.ofReal_pow, EuclideanSpace.real_norm_sq_eq] at hc
  simpa [SmoothBerr.stdGaussianVec, EuclideanSpace.inner_eq_star_dotProduct,
    dotProduct_comm, EuclideanSpace.real_norm_sq_eq, Complex.ofReal_exp, Complex.ofReal_div,
    Complex.ofReal_neg, mul_comm] using hc

lemma weighted_gaussian_fourier_raw {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ)
    (hA : A.PosSemidef) (h : Fin d → ℝ) :
    (∫ y : Fin d → ℝ, (Real.exp (-(y ⬝ᵥ (A *ᵥ y))/2) : ℂ) *
        Complex.exp (Complex.I * (h ⬝ᵥ y : ℝ)) ∂SmoothBerr.stdGaussianVec d) =
      (∏ i, ((Real.sqrt (1+hA.1.eigenvalues i))⁻¹ : ℂ)) *
        Complex.exp (-(∑ i, (inner ℝ (WithLp.toLp 2 h) (hA.1.eigenvectorBasis i))^2 /
          (2*(1+hA.1.eigenvalues i)) : ℝ)) := by
  have hc := quadratic_weighted_gaussian_fourier A hA (WithLp.toLp 2 h)
  rw [← map_pi_eq_stdGaussian,
    integral_map (Measurable.aemeasurable (by fun_prop))
      (Measurable.aestronglyMeasurable (by fun_prop))] at hc
  simpa [SmoothBerr.stdGaussianVec, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.toEuclideanLin_apply, dotProduct_comm] using hc

lemma integrable_bilin_kernel {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) :
    Integrable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      Complex.exp (Complex.I *
        ((p.1 ⬝ᵥ (T *ᵥ p.2) + p.1 ⬝ᵥ (L *ᵥ b) + p.2 ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)))
        ((SmoothBerr.stdGaussianVec d).prod (SmoothBerr.stdGaussianVec d)) := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    (Measurable.aestronglyMeasurable (by fun_prop))
  exact Filter.Eventually.of_forall (fun p => by simp [Complex.norm_exp])

lemma bilinChar_left_weighted {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a : Fin k → ℝ) :
    bilinChar T L a 0 =
      ∫ y : Fin d → ℝ, (Real.exp (-(y ⬝ᵥ ((Tᵀ*T) *ᵥ y))/2) : ℂ) *
        Complex.exp (Complex.I * ((L *ᵥ a) ⬝ᵥ y : ℝ)) ∂SmoothBerr.stdGaussianVec d := by
  unfold bilinChar
  rw [integral_prod_symm _ (integrable_bilin_kernel T L a 0)]
  apply integral_congr_ae
  filter_upwards [] with y
  simp only [mulVec_zero, dotProduct_zero, add_zero]
  have hfactor (x : Fin d → ℝ) :
      Complex.exp (Complex.I * ((x ⬝ᵥ (T *ᵥ y) + y ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (x ⬝ᵥ (T *ᵥ y) : ℝ)) *
        Complex.exp (Complex.I * (y ⬝ᵥ (L *ᵥ a) : ℝ)) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [hfactor]
  rw [integral_mul_const, gaussian_dot_characteristic]
  have hquad : y ⬝ᵥ ((Tᵀ*T) *ᵥ y) = ∑ i, (T *ᵥ y) i^2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, pow_two]
  rw [hquad, dotProduct_comm (L *ᵥ a) y]

lemma bilinChar_swap {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) :
    bilinChar T L a b = bilinChar Tᵀ L b a := by
  unfold bilinChar
  rw [← integral_prod_swap]
  apply integral_congr_ae
  filter_upwards [] with p
  congr 2
  simp only [Prod.swap, dotProduct_transpose_mulVec]
  push_cast
  ring

lemma bilinChar_left_gaussian {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a : Fin k → ℝ) :
    ∃ C q : ℝ, 0 < C ∧ ∀ t : ℝ, bilinChar T L (t • a) 0 =
      ((C * Real.exp (-q*t^2) : ℝ) : ℂ) := by
  let A := Tᵀ*T
  have hA : A.PosSemidef := by
    simpa only [A, conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self T
  let ev : Fin d → ℝ := hA.1.eigenvalues
  let basis : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hA.1.eigenvectorBasis
  let C : ℝ := ∏ i, (Real.sqrt (1+ev i))⁻¹
  let q : ℝ := ∑ i, (inner ℝ (WithLp.toLp 2 (L *ᵥ a)) (basis i))^2 /
    (2*(1+ev i))
  refine ⟨C, q, ?_, fun t => ?_⟩
  · apply Finset.prod_pos
    intro i _
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [hA.eigenvalues_nonneg i]))
  · have hs : (∑ i, (inner ℝ (WithLp.toLp 2 (L *ᵥ (t • a))) (basis i))^2 /
        (2*(1+ev i))) = t^2*q := by
      simp only [mulVec_smul, WithLp.toLp_smul, real_inner_smul_left, mul_pow]
      simp_rw [mul_div_assoc, ← Finset.mul_sum]
      rfl
    rw [bilinChar_left_weighted, weighted_gaussian_fourier_raw A hA]
    change (∏ i, ((Real.sqrt (1+ev i))⁻¹ : ℂ)) *
      Complex.exp (-((∑ i, (inner ℝ (WithLp.toLp 2 (L *ᵥ (t • a))) (basis i))^2 /
        (2*(1+ev i)) : ℝ) : ℂ)) = ((C * Real.exp (-q*t^2) : ℝ) : ℂ)
    rw [hs]
    simp only [Complex.ofReal_mul, Complex.ofReal_exp]
    congr 1
    · simp [C]
    · congr 1
      push_cast
      ring

end GinibrePermanent977.Anticoncentration


open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace NNReal ComplexOrder
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace GinibrePermanent977.Anticoncentration

lemma bilinChar_full_weighted {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ)
    (l : (Fin d → ℝ) →ₗ[ℝ] ℂ)
    (hl : ∀ y, l y = (-(y ⬝ᵥ (Tᵀ *ᵥ (L *ᵥ b))) : ℝ) +
      Complex.I * ((y ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)) :
    bilinChar T L a b = (Real.exp (-(∑ i, (L *ᵥ b) i^2)/2) : ℂ) *
      ∫ y : Fin d → ℝ, (Real.exp (-(y ⬝ᵥ ((Tᵀ*T) *ᵥ y))/2) : ℂ) *
        Complex.exp (l y) ∂SmoothBerr.stdGaussianVec d := by
  unfold bilinChar
  rw [integral_prod_symm _ (integrable_bilin_kernel T L a b), ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  have hfactor (x : Fin d → ℝ) :
      Complex.exp (Complex.I * ((x ⬝ᵥ (T *ᵥ y) + x ⬝ᵥ (L *ᵥ b) + y ⬝ᵥ (L *ᵥ a) : ℝ) : ℂ)) =
      Complex.exp (Complex.I * (x ⬝ᵥ (T *ᵥ y + L *ᵥ b) : ℝ)) *
        Complex.exp (Complex.I * (y ⬝ᵥ (L *ᵥ a) : ℝ)) := by
    rw [← Complex.exp_add]
    simp only [dotProduct_add, Complex.ofReal_add]
    congr 1
    ring
  simp_rw [hfactor]
  rw [integral_mul_const, gaussian_dot_characteristic, hl]
  have hquad : y ⬝ᵥ ((Tᵀ*T) *ᵥ y) = ∑ i, (T *ᵥ y) i^2 := by
    rw [← mulVec_mulVec, dotProduct_mulVec, vecMul_transpose]
    simp [dotProduct, pow_two]
  have hcross : y ⬝ᵥ (Tᵀ *ᵥ (L *ᵥ b)) = ∑ i, (T *ᵥ y) i * (L *ᵥ b) i := by
    rw [dotProduct_transpose_mulVec]
    simp [dotProduct, mul_comm]
  simp only [Complex.ofReal_exp]
  rw [← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hsum : (∑ i, (T *ᵥ y + L *ᵥ b) i^2) =
      (∑ i, (T *ᵥ y) i^2) + 2*(∑ i, (T *ᵥ y) i*(L *ᵥ b) i) +
        (∑ i, (L *ᵥ b) i^2) := by
    simp only [Pi.add_apply, add_sq, Finset.sum_add_distrib, mul_assoc]
    rw [← Finset.mul_sum Finset.univ (fun i => (T *ᵥ y) i*(L *ᵥ b) i) 2]
  rw [hquad, hcross, hsum]
  push_cast
  ring

lemma bilinChar_norm_gaussian {d k : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) :
    ∃ C U V : ℝ, 0 < C ∧ ∀ t s : ℝ,
      ‖bilinChar T L (t • a) (s • b)‖ = C * Real.exp (t^2*U+s^2*V) := by
  let A := Tᵀ*T
  have hA : A.PosSemidef := by
    simpa only [A, conjTranspose_eq_transpose_of_trivial] using Matrix.posSemidef_conjTranspose_mul_self T
  let ev : Fin d → ℝ := hA.1.eigenvalues
  let basis : OrthonormalBasis (Fin d) ℝ (EuclideanSpace ℝ (Fin d)) := hA.1.eigenvectorBasis
  let C : ℝ := ∏ i, (Real.sqrt (1+ev i))⁻¹
  let u : Fin d → ℝ := Tᵀ *ᵥ (L *ᵥ b)
  let v : Fin d → ℝ := L *ᵥ a
  let c : ℝ := ∑ i, (L *ᵥ b) i^2
  let U : ℝ := ∑ i, ((basis i) ⬝ᵥ u)^2 / (2*(1+ev i))
  let V : ℝ := ∑ i, ((basis i) ⬝ᵥ v)^2 / (2*(1+ev i))
  have hC : 0 < C := by
    apply Finset.prod_pos
    intro i _
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith [hA.eigenvalues_nonneg i]))
  refine ⟨C, -V, U-c/2, hC, fun t s => ?_⟩
  let l : (Fin d → ℝ) →ₗ[ℝ] ℂ :=
    { toFun := fun y => (-(s*(y ⬝ᵥ u)) : ℝ) + Complex.I * ((t*(y ⬝ᵥ v) : ℝ) : ℂ)
      map_add' := by intro x y; simp [add_dotProduct, mul_add]; ring
      map_smul' := by
        intro r y
        simp [smul_dotProduct, smul_eq_mul, Complex.real_smul]
        push_cast
        ring }
  have hl (y : Fin d → ℝ) : l y = (-(y ⬝ᵥ (Tᵀ *ᵥ (L *ᵥ (s • b)))) : ℝ) +
      Complex.I * ((y ⬝ᵥ (L *ᵥ (t • a)) : ℝ) : ℂ) := by
    simp [l, u, v, mulVec_smul, dotProduct_smul, smul_eq_mul]
  have hsumsq : (∑ i, (L *ᵥ (s • b)) i^2) = s^2*c := by
    simp only [mulVec_smul, Pi.smul_apply, smul_eq_mul, mul_pow]
    rw [← Finset.mul_sum]
  have hlre (i : Fin d) : ((l (basis i))^2 / (2*(1+ev i) : ℝ)).re =
      (s^2*((basis i) ⬝ᵥ u)^2-t^2*((basis i) ⬝ᵥ v)^2) / (2*(1+ev i)) := by
    simp only [Complex.div_ofReal_re, l, LinearMap.coe_mk, AddHom.coe_mk,
      pow_two, Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, zero_mul, mul_zero, zero_add, add_zero, one_mul, mul_one]
    ring
  have hre : (∑ i, (l (basis i))^2 / (2*(1+ev i) : ℝ)).re = s^2*U-t^2*V := by
    rw [Complex.re_sum]
    simp_rw [hlre, sub_div, mul_div_assoc, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, ← Finset.mul_sum]
  rw [bilinChar_full_weighted T L (t • a) (s • b) l hl,
    weighted_gaussian_mgf_raw A hA l]
  change ‖(Real.exp (-(∑ i, (L *ᵥ (s • b)) i^2)/2) : ℂ) *
    ((∏ i, ((Real.sqrt (1+ev i))⁻¹ : ℂ)) *
      Complex.exp (∑ i, (l (basis i))^2 / (2*(1+ev i) : ℝ)))‖ = _
  have hcc : (∏ i, ((Real.sqrt (1+ev i))⁻¹ : ℂ)) = (C : ℂ) := by simp [C]
  rw [hsumsq, hcc, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs, abs_of_pos hC,
    Complex.norm_exp, hre]
  rw [mul_left_comm, ← Real.exp_add]
  congr 2
  ring

end GinibrePermanent977.Anticoncentration


open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators ComplexOrder
open GinibrePermanent977.Anticoncentration
set_option autoImplicit false

theorem solution {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (T : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    ‖bilinChar T L (Real.sqrt θ • a) (Real.sqrt (1 - θ) • b)‖ =
      (bilinChar T L a 0).re ^ θ * (bilinChar T L 0 b).re ^ (1 - θ) := by
  obtain ⟨C,U,V,hC,hn⟩ := bilinChar_norm_gaussian T L a b
  have hp := lemma_3_1_quadratic_scaling hd hk T L a b
  have haNorm : ‖bilinChar T L a 0‖ = (bilinChar T L a 0).re := by
    have he := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hp.1.le)
    simpa using he.symm
  have hbNorm : ‖bilinChar T L 0 b‖ = (bilinChar T L 0 b).re := by
    have he := congrArg Complex.re (Complex.eq_coe_norm_of_nonneg hp.2.1.le)
    simpa using he.symm
  have h10 : (bilinChar T L a 0).re = C*Real.exp U := by
    rw [← haNorm]
    simpa using hn 1 0
  have h01 : (bilinChar T L 0 b).re = C*Real.exp V := by
    rw [← hbNorm]
    simpa using hn 0 1
  rw [hn, Real.sq_sqrt hθ0, Real.sq_sqrt (sub_nonneg.mpr hθ1), h10, h01]
  have hcp : C^θ*C^(1-θ) = C := by
    rw [← Real.rpow_add hC]
    norm_num
  calc
    C*Real.exp (θ*U+(1-θ)*V) =
        (C^θ*C^(1-θ)) * ((Real.exp U)^θ*(Real.exp V)^(1-θ)) := by
      rw [hcp, ← Real.exp_mul, ← Real.exp_mul, ← Real.exp_add]
      congr 2
      ring
    _ = (C*Real.exp U)^θ*(C*Real.exp V)^(1-θ) := by
      rw [Real.mul_rpow hC.le (Real.exp_pos U).le,
        Real.mul_rpow hC.le (Real.exp_pos V).le]
      ring
