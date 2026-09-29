-- Prove2me | solution 1 for HairerSPDE.charFun_tilt_of_joint_gaussian
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T23:17:05.49897+00:00
-- url     : https://prove2.me/submissions/4a52deda-e843-4f98-b2a6-988fdb18e112

import Mathlib
import Definitions.Def_HairerSPDE_CameronMartin

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology

private theorem gaussian_pair_of_combinations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X Y : Ω → ℝ) (hX : Measurable X) (hY : Measurable Y)
    (hg : ∀ a b : ℝ, μ.map (fun x => a * X x + b * Y x) =
      gaussianReal 0 (variance (fun x => a * X x + b * Y x) μ).toNNReal) :
    HasGaussianLaw (fun x => (X x, Y x)) μ := by
  constructor
  apply isGaussian_of_map_eq_gaussianReal
  intro K
  let a := K (1, 0)
  let b := K (0, 1)
  refine ⟨0, (variance (fun x => a * X x + b * Y x) μ).toNNReal, ?_⟩
  rw [Measure.map_map K.continuous.measurable (hX.prodMk hY)]
  have hk (x : Ω) : K (X x, Y x) = a * X x + b * Y x := by
    have hp : (X x, Y x) = X x • (1, 0) + Y x • (0, 1) := by
      ext <;> simp
    rw [hp, map_add, map_smul, map_smul]
    simp only [smul_eq_mul]
    dsimp [a, b]
    ring
  convert hg a b using 1
  congr 1
  funext x
  exact hk x

private theorem gaussian_mixed_transform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X Y : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 μ)
    (mX : ∫ x, X x ∂μ = 0) (mY : ∫ x, Y x ∂μ = 0)
    (hg : ∀ a b : ℝ, μ.map (fun x => a * X x + b * Y x) =
      gaussianReal 0 (variance (fun x => a * X x + b * Y x) μ).toNNReal) :
    (∫ x, Complex.exp ((X x : ℂ) * Complex.I + Y x) ∂μ) =
      Complex.exp (-(variance X μ : ℂ) / 2 + variance Y μ / 2 +
        (covariance X Y μ : ℂ) * Complex.I) := by
  have gp := gaussian_pair_of_combinations μ X Y hX hY hg
  have gx : μ.map X = gaussianReal 0 (variance X μ).toNNReal := by
    simpa using hg 1 0
  have gy : μ.map Y = gaussianReal 0 (variance Y μ).toNNReal := by
    simpa using hg 0 1
  by_cases hv : variance Y μ = 0
  · have hy0 : ∀ᵐ x ∂μ, Y x = 0 := by
      simpa [mY] using ae_eq_integral_of_variance_eq_zero hY2 hv
    have hc : covariance X Y μ = 0 := by
      unfold covariance
      apply integral_eq_zero_of_ae
      filter_upwards [hy0] with x hx
      simp [hx, mY]
    calc
      (∫ x, Complex.exp ((X x : ℂ) * Complex.I + Y x) ∂μ) =
          complexMGF X μ Complex.I := by
        apply integral_congr_ae
        filter_upwards [hy0] with x hx
        simp [hx, mul_comm]
      _ = _ := by
        rw [complexMGF_gaussianReal gx]
        simp [hv, hc, Real.coe_toNNReal _ (variance_nonneg X μ), Complex.I_sq]
  · let c : ℝ := covariance X Y μ / variance Y μ
    let Z : Ω → ℝ := fun x => X x - c * Y x
    have hZ : Measurable Z := hX.sub (hY.const_mul c)
    have hZ2 : MemLp Z 2 μ := hX2.sub (hY2.const_mul c)
    have mZ : ∫ x, Z x ∂μ = 0 := by
      dsimp [Z]
      rw [integral_sub (hX2.integrable (by norm_num))
        ((hY2.integrable (by norm_num)).const_mul c), integral_const_mul, mX, mY]
      ring
    have gz : μ.map Z = gaussianReal 0 (variance Z μ).toNNReal := by
      simpa [Z, sub_eq_add_neg] using hg 1 (-c)
    have hcomb : ∀ a b : ℝ, μ.map (fun x => a * Z x + b * Y x) =
        gaussianReal 0 (variance (fun x => a * Z x + b * Y x) μ).toNNReal := by
      intro a b
      have he : (fun x => a * Z x + b * Y x) =
          (fun x => a * X x + (b - a * c) * Y x) := by
        funext x
        dsimp [Z]
        ring
      rw [he]
      exact hg a (b - a * c)
    have hzY : covariance Z Y μ = 0 := by
      dsimp [Z]
      rw [covariance_fun_sub_left hX2 (hY2.const_mul c) hY2,
        covariance_const_mul_left, covariance_self hY.aemeasurable]
      dsimp [c]
      rw [div_mul_cancel₀ _ hv, sub_self]
    have hind := (gaussian_pair_of_combinations μ Z Y hZ hY hcomb).indepFun_of_covariance_eq_zero hzY
    have hvar : variance Z μ = variance X μ - 2 * c * covariance X Y μ +
        c ^ 2 * variance Y μ := by
      dsimp [Z]
      rw [variance_fun_sub hX2 (hY2.const_mul c), covariance_const_mul_right,
        variance_const_mul]
      ring
    have hfactor : (∫ x, Complex.exp ((X x : ℂ) * Complex.I + Y x) ∂μ) =
        complexMGF Z μ Complex.I * complexMGF Y μ (1 + (c : ℂ) * Complex.I) := by
      calc
        _ = ∫ x, Complex.exp (Complex.I * (Z x : ℂ)) *
            Complex.exp ((1 + (c : ℂ) * Complex.I) * (Y x : ℂ)) ∂μ := by
          apply integral_congr_ae
          filter_upwards [] with x
          rw [← Complex.exp_add]
          congr 1
          dsimp [Z]
          push_cast
          ring
        _ = _ := hind.integral_fun_comp_mul_comp
          (f := fun t : ℝ => Complex.exp (Complex.I * (t : ℂ)))
          (g := fun t : ℝ => Complex.exp ((1 + (c : ℂ) * Complex.I) * (t : ℂ)))
          hZ.aemeasurable hY.aemeasurable
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
          (Complex.continuous_exp.comp
            (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
    rw [hfactor, complexMGF_gaussianReal gz, complexMGF_gaussianReal gy,
      ← Complex.exp_add]
    congr 1
    rw [Real.coe_toNNReal _ (variance_nonneg Z μ),
      Real.coe_toNNReal _ (variance_nonneg Y μ), hvar]
    have hc : c * variance Y μ = covariance X Y μ := by
      dsimp [c]
      exact div_mul_cancel₀ _ hv
    have hc' : (c : ℂ) * (variance Y μ : ℂ) = (covariance X Y μ : ℂ) := by
      exact_mod_cast hc
    push_cast
    simp only [mul_zero, zero_add]
    simp only [add_sq, mul_pow, Complex.I_sq]
    linear_combination (Complex.I - (c : ℂ)) * hc'

theorem solution {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B] [MeasurableSpace B]
    [BorelSpace B] [CompleteSpace B] [SecondCountableTopology B]
    (μ : Measure B) [IsGaussian μ] (hμ : μ[id] = 0) (h : B) (h' : B → ℝ)
    (h'meas : Measurable h') (h'mem : MemLp h' 2 μ)
    (h'rep : ∀ L : StrongDual ℝ B, ∫ x, h' x * L x ∂μ = L h)
    (hjoint : ∀ (L : StrongDual ℝ B) (a b : ℝ),
      μ.map (fun x => a * L x + b * h' x) =
        gaussianReal 0 ((ProbabilityTheory.variance (fun x => a * L x + b * h' x) μ).toNNReal)) :
    IsFiniteMeasure (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2))))
    ∧ ∀ L : StrongDual ℝ B, charFunDual (μ.withDensity (fun x : B => ENNReal.ofReal (Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)))) L = Complex.exp ((L h) * Complex.I - covarianceBilinDual μ L L / 2) := by
  have gy : μ.map h' = gaussianReal 0 (variance h' μ).toNNReal := by
    simpa using hjoint 0 0 1
  have my : ∫ x, h' x ∂μ = 0 := by
    have hi := integral_id_gaussianReal (μ := (0 : ℝ)) (v := (variance h' μ).toNNReal)
    rw [← gy, integral_map h'meas.aemeasurable (by fun_prop)] at hi
    exact hi
  have vy : variance h' μ = ∫ x, (h' x) ^ 2 ∂μ :=
    variance_of_integral_eq_zero h'meas.aemeasurable my
  have hexp : Integrable (fun x => Real.exp (h' x)) μ := by
    have he := integrable_exp_mul_gaussianReal (μ := (0 : ℝ))
      (v := (variance h' μ).toNNReal) 1
    simp only [one_mul] at he
    rw [← gy] at he
    exact he.comp_aemeasurable h'meas.aemeasurable
  have hd : Integrable (fun x => Real.exp (h' x - (∫ y, (h' y) ^ 2 ∂μ) / 2)) μ := by
    simpa only [Real.exp_sub, div_eq_mul_inv] using
      hexp.mul_const (Real.exp ((∫ y, (h' y) ^ 2 ∂μ) / 2))⁻¹
  refine ⟨isFiniteMeasure_withDensity_ofReal hd.hasFiniteIntegral, ?_⟩
  intro L
  have hl2 : MemLp (fun x => L x) 2 μ := IsGaussian.memLp_dual μ L 2 (by norm_num)
  have ml : ∫ x, L x ∂μ = 0 := by
    rw [IsGaussian.integral_dual L]
    change L (∫ x, id x ∂μ) = 0
    rw [hμ, map_zero]
  have hc : covariance (fun x => L x) h' μ = L h := by
    rw [covariance, ml, my]
    simpa only [sub_zero, mul_comm] using h'rep L
  have hv : covarianceBilinDual μ L L = variance (fun x => L x) μ :=
    covarianceBilinDual_self_eq_variance (IsGaussian.memLp_two_id) L
  have ht := gaussian_mixed_transform μ (fun x => L x) h' L.continuous.measurable
    h'meas hl2 h'mem ml my (hjoint L)
  rw [charFunDual_apply, integral_withDensity_eq_integral_toReal_smul
    (by fun_prop) (by filter_upwards [] with x; exact ENNReal.ofReal_lt_top)]
  calc
    _ = (∫ x, Complex.exp ((L x : ℂ) * Complex.I + h' x) ∂μ) *
        Complex.exp (-(((∫ y, (h' y) ^ 2 ∂μ) : ℝ) : ℂ) / 2) := by
      rw [← integral_mul_const]
      apply integral_congr_ae
      filter_upwards [] with x
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
      simp only [Complex.real_smul, Complex.ofReal_exp]
      rw [← Complex.exp_add, ← Complex.exp_add]
      congr 1
      simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    _ = _ := by
      rw [ht, ← Complex.exp_add, hc, hv, vy]
      congr 1
      ring
