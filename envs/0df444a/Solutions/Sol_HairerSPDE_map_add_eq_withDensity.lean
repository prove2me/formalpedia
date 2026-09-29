-- Prove2me | solution 1 for HairerSPDE.map_add_eq_withDensity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-13T17:38:47.013707+00:00
-- url     : https://prove2.me/submissions/0dabc16c-45cb-4688-bf01-bd6bf5cf4991

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

namespace HairerSPDE

private lemma bilin_cross_eq_zero_of_self_eq_zero {E : Type*} [AddCommGroup E]
    [Module ℝ E] (Q : LinearMap.BilinForm ℝ E) (hQ : Q.IsPosSemidef)
    {x : E} (hx : Q x x = 0) (y : E) : Q x y = 0 := by
  let b : ℝ := Q x y
  let c : ℝ := Q y y
  have hc : 0 ≤ c := hQ.nonneg y
  by_cases hc0 : c = 0
  · have hp := hQ.nonneg (x + y)
    have hm := hQ.nonneg (x - y)
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply] at hp hm
    dsimp only [c] at hc0
    rw [hx, hc0, hQ.eq y x] at hp hm
    linarith
  · have hcpos : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hz := hQ.nonneg (x - (b / c) • y)
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul] at hz
    rw [hx, hQ.eq y x] at hz
    dsimp only [b, c] at hz ⊢
    have hcne : Q y y ≠ 0 := by simpa [c] using hc0
    have hcpos' : 0 < Q y y := by simpa [c] using hcpos
    field_simp [hcne] at hz
    ring_nf at hz
    nlinarith [sq_nonneg (Q x y)]

private lemma centered_dual_complexMGF {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B] (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (L : StrongDual ℝ B) (z : ℂ) :
    ∫ x, Complex.exp (z * L x) ∂μ =
      Complex.exp ((covarianceBilinDual μ L L : ℂ) * z ^ 2 / 2) := by
  have hmean : ∫ x, x ∂μ = (0 : B) := by simpa only [id_eq] using hμ
  have hmap := IsGaussian.map_eq_gaussianReal (μ := μ) L
  have hvar : Var[(L : B → ℝ); μ] = covarianceBilinDual μ L L := by
    exact (covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id L).symm
  have hLmean : ∫ x, L x ∂μ = 0 := by
    simpa [IsGaussian.integral_dual, hmean]
  change complexMGF (L : B → ℝ) μ z = _
  rw [complexMGF_gaussianReal hmap z]
  rw [hLmean, hvar]
  simp [Real.coe_toNNReal', covarianceBilinDual_self_nonneg]

private lemma centered_dual_mgf {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B] (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (L : StrongDual ℝ B) (t : ℝ) :
    ∫ x, Real.exp (t * L x) ∂μ =
      Real.exp (covarianceBilinDual μ L L * t ^ 2 / 2) := by
  have hmean : ∫ x, x ∂μ = (0 : B) := by simpa only [id_eq] using hμ
  have hmap := IsGaussian.map_eq_gaussianReal (μ := μ) L
  have hvar : Var[(L : B → ℝ); μ] = covarianceBilinDual μ L L := by
    exact (covarianceBilinDual_self_eq_variance IsGaussian.memLp_two_id L).symm
  have hLmean : ∫ x, L x ∂μ = 0 := by
    simpa [IsGaussian.integral_dual, hmean]
  change mgf (L : B → ℝ) μ t = _
  rw [mgf_gaussianReal hmap t, hLmean, hvar]
  simp [Real.coe_toNNReal', covarianceBilinDual_self_nonneg]

private lemma centered_dual_exp_char {B : Type*} [NormedAddCommGroup B]
    [NormedSpace ℝ B] [MeasurableSpace B] [BorelSpace B] [CompleteSpace B]
    [SecondCountableTopology B] (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0)
    (A L : StrongDual ℝ B) :
    ∫ x, (Real.exp (A x - covarianceBilinDual μ A A / 2) : ℂ) *
        Complex.exp (L x * Complex.I) ∂μ =
      Complex.exp (covarianceBilinDual μ A L * Complex.I -
        covarianceBilinDual μ L L / 2) := by
  let Q := covarianceBilinDual μ
  let v : ℝ := Q A A
  let c : ℝ := Q A L
  have hv : 0 ≤ v := covarianceBilinDual_self_nonneg A
  let a : ℝ := if v = 0 then 0 else c / v
  have hca : c = a * v := by
    by_cases hv0 : v = 0
    · have hc0 : c = 0 := by
        exact bilin_cross_eq_zero_of_self_eq_zero Q.toBilinForm
          isPosSemidef_covarianceBilinDual hv0 L
      simp [a, hv0, hc0]
    · simp [a, hv0]
  let Z : StrongDual ℝ B := L - a • A
  have hcovQ : Q A Z = 0 := by
    change Q A (L - a • A) = 0
    simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    change c - a * v = 0
    rw [← hca]
    ring
  have hcov : cov[(A : B → ℝ), (Z : B → ℝ); μ] = 0 := by
    rw [← covarianceBilinDual_eq_covariance IsGaussian.memLp_two_id]
    exact hcovQ
  have hjoint : HasGaussianLaw (fun x : B ↦ (A x, Z x)) μ := by
    simpa only [id_eq, ContinuousLinearMap.prod_apply] using
      (IsGaussian.hasGaussianLaw_id (μ := μ)).map_fun (A.prod Z)
  have hindep : IndepFun (A : B → ℝ) (Z : B → ℝ) μ :=
    hjoint.indepFun_of_covariance_eq_zero hcov
  let z : ℂ := 1 + (a : ℂ) * Complex.I
  have hfactor :
      ∫ x, Complex.exp (z * A x) * Complex.exp (Complex.I * Z x) ∂μ =
        (∫ x, Complex.exp (z * A x) ∂μ) *
          ∫ x, Complex.exp (Complex.I * Z x) ∂μ := by
    simpa only [Function.comp_apply] using
      hindep.integral_fun_comp_mul_comp
        (by fun_prop : AEMeasurable (A : B → ℝ) μ)
        (by fun_prop : AEMeasurable (Z : B → ℝ) μ)
        (by fun_prop : AEStronglyMeasurable (fun t : ℝ ↦ Complex.exp (z * t)) (μ.map A))
        (by fun_prop : AEStronglyMeasurable
          (fun t : ℝ ↦ Complex.exp (Complex.I * t)) (μ.map Z))
  have hmgfA := centered_dual_complexMGF μ hμ A z
  have hmgfZ := centered_dual_complexMGF μ hμ Z Complex.I
  have hvar : Q L L = a ^ 2 * v + Q Z Z := by
    have hL : L = a • A + Z := by
      ext x
      simp [Z]
    conv_lhs => rw [hL]
    simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul]
    rw [hcovQ, show Q Z A = Q A Z from covarianceBilinDual_comm Z A, hcovQ]
    ring
  calc
    (∫ x, (Real.exp (A x - covarianceBilinDual μ A A / 2) : ℂ) *
        Complex.exp (L x * Complex.I) ∂μ) =
        Complex.exp (-(v : ℂ) / 2) *
          ∫ x, Complex.exp (z * A x) * Complex.exp (Complex.I * Z x) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with x
      have hLx : L x = a * A x + Z x := by
        simp [Z]
      rw [← Complex.exp_add, ← Complex.exp_add, hLx]
      simp only [Complex.ofReal_exp]
      rw [← Complex.exp_add]
      congr 1
      dsimp only [Q, v, z]
      push_cast
      ring
    _ = Complex.exp (-(v : ℂ) / 2) *
        (Complex.exp ((v : ℂ) * z ^ 2 / 2) *
          Complex.exp ((Q Z Z : ℂ) * Complex.I ^ 2 / 2)) := by
      rw [hfactor, hmgfA, hmgfZ]
    _ = Complex.exp (covarianceBilinDual μ A L * Complex.I -
        covarianceBilinDual μ L L / 2) := by
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      have hcaC := congrArg (fun x : ℝ ↦ (x : ℂ)) hca
      have hvarC := congrArg (fun x : ℝ ↦ (x : ℂ)) hvar
      dsimp only [Q, v, c] at hcaC hvarC ⊢
      dsimp only [z]
      push_cast at hcaC hvarC ⊢
      rw [hcaC, hvarC]
      apply Complex.ext <;>
        simp [pow_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem mapAddEqWithDensity {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    [MeasurableSpace B] [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B, covarianceBilinDual μ h' L = L h) :
    μ.map (fun x ↦ x + h) =
      μ.withDensity
        (fun x ↦ ENNReal.ofReal
          (Real.exp (h' x - covarianceBilinDual μ h' h' / 2))) := by
  let q : ℝ := covarianceBilinDual μ h' h'
  let d : B → ℝ≥0∞ := fun x ↦ ENNReal.ofReal (Real.exp (h' x - q / 2))
  have hd_meas : Measurable d := by fun_prop
  have hd_top : ∀ x, d x < ∞ := by
    intro x
    simp [d]
  have hmap := IsGaussian.map_eq_gaussianReal (μ := μ) h'
  have hexp_map : Integrable (fun y : ℝ ↦ Real.exp y) (μ.map h') := by
    rw [hmap]
    simpa using (integrable_exp_mul_gaussianReal
      (μ := ∫ x, h' x ∂μ) (v := Var[(h' : B → ℝ); μ].toNNReal) 1)
  have hexp : Integrable (fun x : B ↦ Real.exp (h' x)) μ := by
    have hc := (integrable_map_measure
      (by fun_prop : AEStronglyMeasurable (fun y : ℝ ↦ Real.exp y) (μ.map h'))
      (by fun_prop : AEMeasurable (h' : B → ℝ) μ)).mp hexp_map
    simpa only [Function.comp_def] using hc
  have hd_int : Integrable (fun x : B ↦ Real.exp (h' x - q / 2)) μ := by
    have hc := hexp.const_mul (Real.exp (-q / 2))
    convert hc using 1
    funext x
    rw [← Real.exp_add]
    congr 1
    ring
  have hd_integral : ∫ x, Real.exp (h' x - q / 2) ∂μ = 1 := by
    calc
      (∫ x, Real.exp (h' x - q / 2) ∂μ) =
          Real.exp (-q / 2) * ∫ x, Real.exp (h' x) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with x
        rw [← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-q / 2) * Real.exp (q / 2) := by
        rw [show (∫ x, Real.exp (h' x) ∂μ) = Real.exp (q / 2) by
          simpa [q] using centered_dual_mgf μ hμ h' 1]
      _ = 1 := by
        rw [← Real.exp_add]
        ring_nf
        exact Real.exp_zero
  have hd_lintegral : ∫⁻ x, d x ∂μ = 1 := by
    dsimp only [d]
    rw [← ofReal_integral_eq_lintegral_ofReal hd_int
      (ae_of_all _ fun x ↦ (Real.exp_pos _).le), hd_integral]
    norm_num
  letI : IsFiniteMeasure (μ.withDensity d) :=
    isFiniteMeasure_withDensity (by rw [hd_lintegral]; norm_num)
  change μ.map (fun x ↦ x + h) = μ.withDensity d
  apply Measure.ext_of_charFunDual
  funext L
  rw [charFunDual_map_add_const]
  rw [IsGaussian.charFunDual_eq' L, hμ]
  simp only [map_zero, zero_mul, zero_sub]
  rw [charFunDual_apply,
    integral_withDensity_eq_integral_toReal_smul hd_meas (ae_of_all _ hd_top)]
  simp only [d, ENNReal.toReal_ofReal (Real.exp_pos _).le, Complex.real_smul]
  rw [centered_dual_exp_char μ hμ h' L, hh' L]
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring

end HairerSPDE

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : StrongDual ℝ B)
    (hh' : ∀ L : StrongDual ℝ B, covarianceBilinDual μ h' L = L h) :
    μ.map (fun x ↦ x + h)
      = μ.withDensity
          (fun x ↦ ENNReal.ofReal (Real.exp (h' x - covarianceBilinDual μ h' h' / 2))) :=
  HairerSPDE.mapAddEqWithDensity μ hμ h h' hh'
