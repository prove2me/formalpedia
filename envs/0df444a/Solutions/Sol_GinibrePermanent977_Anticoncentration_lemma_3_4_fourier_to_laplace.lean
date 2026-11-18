-- Prove2me | solution 1 for GinibrePermanent977.Anticoncentration.lemma_3_4_fourier_to_laplace
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-17T23:04:18.648558+00:00
-- url     : https://prove2.me/submissions/9c314938-627b-463a-a98c-392690edcb7a

import Definitions.Def_GinibrePermanent977_Anticoncentration_Model

open MeasureTheory ProbabilityTheory Matrix
open scoped BigOperators RealInnerProductSpace
set_option autoImplicit false

namespace GinibrePermanent977.Anticoncentration

private lemma quadForm_real {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (x : Fin d → ℝ) : quadForm T x = x ⬝ᵥ (T *ᵥ x) := by
  simp [quadForm, realInner, dotProduct, mul_comm]

private lemma integrable_cos_dot {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → Fin d → ℝ)
    (g : Ω → Fin d → ℝ) (hf : Measurable f) (hg : Measurable g) :
    Integrable (fun p => Real.cos (f p ⬝ᵥ g p)) μ := by
  apply Integrable.mono' (integrable_const (1 : ℝ))
    ((by fun_prop : Measurable (fun p => Real.cos (f p ⬝ᵥ g p))).aestronglyMeasurable)
  exact Filter.Eventually.of_forall (fun p => by simpa using Real.abs_cos_le_one (f p ⬝ᵥ g p))

private lemma re_exp_integral {d : ℕ} (μ : Measure (Fin d → ℝ)) [IsFiniteMeasure μ]
    (t : Fin d → ℝ) :
    (∫ x, Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ)) ∂μ).re =
      ∫ x, Real.cos (t ⬝ᵥ x) ∂μ := by
  have hi : Integrable (fun x : Fin d → ℝ =>
      Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ))) μ := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((by fun_prop : Measurable (fun x : Fin d → ℝ =>
        Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ)))).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun x => by simp [Complex.norm_exp])
  have hr : (∫ x, Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ)) ∂μ).re =
      ∫ x, (Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ))).re ∂μ :=
    (integral_re hi).symm
  rw [hr]
  congr 1
  ext x
  simp [Complex.exp_re, mul_comm Complex.I]

private lemma gaussian_cos_quad {d : ℕ} (T : Matrix (Fin d) (Fin d) ℝ)
    (hT : T.PosSemidef) (x : Fin d → ℝ) :
    ∫ t : EuclideanSpace ℝ (Fin d), Real.cos ((fun i => t i) ⬝ᵥ x)
      ∂multivariateGaussian 0 ((2 : ℝ) • T) = Real.exp (-quadForm T x) := by
  have hs : ((2 : ℝ) • T).PosSemidef := hT.smul (by norm_num)
  have hc := charFun_multivariateGaussian (μ := (0 : EuclideanSpace ℝ (Fin d))) hs
    (WithLp.toLp 2 x)
  have hi : Integrable (fun t : EuclideanSpace ℝ (Fin d) =>
      Complex.exp (((inner ℝ t (WithLp.toLp 2 x)) : ℂ) * Complex.I))
      (multivariateGaussian 0 ((2 : ℝ) • T)) := by
    apply Integrable.mono' (integrable_const (1 : ℝ))
      ((by fun_prop : Measurable (fun t : EuclideanSpace ℝ (Fin d) =>
        Complex.exp (((inner ℝ t (WithLp.toLp 2 x)) : ℂ) * Complex.I))).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun t => by simp [Complex.norm_exp])
  have hr := congrArg Complex.re hc
  rw [charFun_apply] at hr
  have hre : (∫ t : EuclideanSpace ℝ (Fin d),
      Complex.exp (((inner ℝ t (WithLp.toLp 2 x)) : ℂ) * Complex.I)
      ∂multivariateGaussian 0 ((2 : ℝ) • T)).re =
      ∫ t : EuclideanSpace ℝ (Fin d),
      (Complex.exp (((inner ℝ t (WithLp.toLp 2 x)) : ℂ) * Complex.I)).re
      ∂multivariateGaussian 0 ((2 : ℝ) • T) := (integral_re hi).symm
  rw [hre] at hr
  simpa [Complex.exp_re, EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm,
    quadForm_real, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, mul_div_cancel_left₀] using hr

end GinibrePermanent977.Anticoncentration

open GinibrePermanent977.Anticoncentration

theorem solution {d : ℕ} (μ ν : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (h : ∀ t : Fin d → ℝ,
      (∫ x, Complex.exp (Complex.I * ((t ⬝ᵥ x : ℝ) : ℂ)) ∂μ).re ≤
        (∫ y, Complex.exp (Complex.I * ((t ⬝ᵥ y : ℝ) : ℂ)) ∂ν).re) :
    OuterLaplaceOrder ν μ (fun y => y) (fun x => x) := by
  intro T hT
  have hpsd : T.PosSemidef := by
    refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨hT.1, ?_⟩
    intro x
    simpa [quadForm_real] using hT.2 x
  let ρ := multivariateGaussian (0 : EuclideanSpace ℝ (Fin d)) ((2 : ℝ) • T)
  let f := fun (t : EuclideanSpace ℝ (Fin d)) (x : Fin d → ℝ) =>
    Real.cos ((fun i => t i) ⬝ᵥ x)
  have hf (η : Measure (Fin d → ℝ)) [IsProbabilityMeasure η] :
      Integrable (Function.uncurry f) (ρ.prod η) := by
    exact integrable_cos_dot (ρ.prod η)
      (fun p => fun i => p.1 i) (fun p => p.2) (by fun_prop) (by fun_prop)
  have he (x : Fin d → ℝ) : ∫ t, f t x ∂ρ = Real.exp (-quadForm T x) :=
    gaussian_cos_quad T hpsd x
  calc
    (∫ x, Real.exp (-quadForm T x) ∂μ) = ∫ x, ∫ t, f t x ∂ρ ∂μ := by
      simp_rw [he]
    _ = ∫ t, ∫ x, f t x ∂μ ∂ρ := (integral_integral_swap (hf μ)).symm
    _ ≤ ∫ t, ∫ y, f t y ∂ν ∂ρ := by
      apply integral_mono (hf μ).integral_prod_left (hf ν).integral_prod_left
      intro t
      simpa only [re_exp_integral, f, Function.uncurry] using h (fun i => t i)
    _ = ∫ y, ∫ t, f t y ∂ρ ∂ν := integral_integral_swap (hf ν)
    _ = ∫ y, Real.exp (-quadForm T y) ∂ν := by simp_rw [he]

