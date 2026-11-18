-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.lemma_3_1_quadratic_scaling
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:25:00.527045+00:00
-- url     : https://prove2.me/submissions/ddebabe6-72a5-45b9-9abe-ee189f9afb77

import Theorems.Thm_GinibrePermanent977_Anticoncentration_quadratic_weighted_gaussian_fourier
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
open scoped BigOperators ComplexOrder
open GinibrePermanent977.Anticoncentration
set_option autoImplicit false

theorem solution {d k : ℕ} (hd : 1 ≤ d) (hk : 1 ≤ k)
    (T : Matrix (Fin d) (Fin d) ℝ) (L : Matrix (Fin d) (Fin k) ℝ) (a b : Fin k → ℝ) :
    0 < bilinChar T L a 0 ∧ 0 < bilinChar T L 0 b ∧
      ∀ t : ℝ,
        (bilinChar T L (t • a) 0).re / (bilinChar T L 0 0).re =
            ((bilinChar T L a 0).re / (bilinChar T L 0 0).re) ^ (t ^ 2) ∧
          (bilinChar T L 0 (t • b)).re / (bilinChar T L 0 0).re =
            ((bilinChar T L 0 b).re / (bilinChar T L 0 0).re) ^ (t ^ 2) := by
  obtain ⟨C,q,hC,hleft⟩ := bilinChar_left_gaussian T L a
  obtain ⟨D,r,hD,hright⟩ := bilinChar_left_gaussian Tᵀ L b
  have hright' (t : ℝ) : bilinChar T L 0 (t • b) =
      ((D * Real.exp (-r*t^2) : ℝ) : ℂ) := by
    rw [bilinChar_swap]
    exact hright t
  have h00C : bilinChar T L 0 0 = (C : ℂ) := by simpa using hleft 0
  have h00D : bilinChar T L 0 0 = (D : ℂ) := by simpa using hright' 0
  have h10 : bilinChar T L a 0 = ((C*Real.exp (-q) : ℝ) : ℂ) := by simpa using hleft 1
  have h01 : bilinChar T L 0 b = ((D*Real.exp (-r) : ℝ) : ℂ) := by simpa using hright' 1
  refine ⟨?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · rw [h10]
    exact_mod_cast mul_pos hC (Real.exp_pos (-q))
  · rw [h01]
    exact_mod_cast mul_pos hD (Real.exp_pos (-r))
  · rw [hleft t, h10, h00C]
    simp only [Complex.ofReal_re]
    simp only [mul_div_cancel_left₀ _ hC.ne']
    rw [← Real.exp_mul]
  · rw [hright' t, h01, h00D]
    simp only [Complex.ofReal_re]
    simp only [mul_div_cancel_left₀ _ hD.ne']
    rw [← Real.exp_mul]
