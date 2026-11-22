-- Prove2me | solution 1 for Kyprianou.Ch01.lundbergRootEquation
-- status  : ACCEPTED   (prove)
-- author  : @coqelz
-- created : 2026-11-21T09:34:15.49599+00:00
-- url     : https://prove2.me/submissions/b8efb052-0cc7-4dd6-aedf-f5eae8a77494

import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Mathlib
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Theorems.Thm_Kyprianou_Ch01_compoundPoissonCharExponent
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false
set_option linter.style.haveILetI false
universe u

open QueueingFundamentals.MG1 (convPow)

theorem lre_convPow_isProb (F : Measure ℝ) [IsProbabilityMeasure F] :
    ∀ n, IsProbabilityMeasure (convPow F n)
  | 0 => by
      show IsProbabilityMeasure (Measure.dirac (0 : ℝ))
      infer_instance
  | n + 1 => by
      haveI := lre_convPow_isProb F n
      show IsProbabilityMeasure ((convPow F n).conv F)
      infer_instance

theorem lre_charFun_convPow (F : Measure ℝ) [IsProbabilityMeasure F] (t : ℝ) :
    ∀ n, charFun (convPow F n) t = charFun F t ^ n
  | 0 => by
      show charFun (Measure.dirac (0 : ℝ)) t = _
      simp [charFun_dirac]
  | n + 1 => by
      haveI := lre_convPow_isProb F n
      show charFun ((convPow F n).conv F) t = _
      rw [charFun_conv, lre_charFun_convPow F t n, pow_succ]

theorem lre_lintegral_exp_convPow (F : Measure ℝ) [IsProbabilityMeasure F] (θ : ℝ) :
    ∀ n, ∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂(convPow F n) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (θ * x)) ∂F) ^ n
  | 0 => by
      show ∫⁻ x, _ ∂(Measure.dirac (0 : ℝ)) = _
      simp
  | n + 1 => by
      haveI := lre_convPow_isProb F n
      show ∫⁻ x, _ ∂((convPow F n).conv F) = _
      rw [Measure.lintegral_conv (by fun_prop)]
      simp_rw [mul_add, Real.exp_add, ENNReal.ofReal_mul (Real.exp_pos _).le]
      simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      rw [lintegral_mul_const _ (by fun_prop), lre_lintegral_exp_convPow F θ n, pow_succ]

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (premium : ℝ) (hpremium : 0 < premium)
    (nu : ℝ) (hnu : 0 < nu)
    (hint : Integrable
      (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) P)
    (hroot : (∫ ω, Real.exp
      (-nu * riskSurplus arrival claims premium 0 1 ω) ∂P) = 1) :
    Integrable (fun x : ℝ => Real.exp (nu * x)) F ∧
      (rate : ℝ) * (∫ x, (Real.exp (nu * x) - 1) ∂F) = premium * nu := by
  -- the aggregate claim at time one
  set S : Ω → ℝ := fun ω => compoundPoisson 0 arrival claims ((1 : ℝ≥0) : ℝ) ω with hS
  have hR : ∀ ω, riskSurplus arrival claims premium 0 1 ω = premium - S ω := by
    intro ω; simp [riskSurplus, aggregateClaims, hS]
  have hexpR : ∀ ω, Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω) =
      Real.exp (-nu * premium) * Real.exp (nu * S ω) := by
    intro ω; rw [hR, ← Real.exp_add]; ring_nf
  -- S is a.e.-measurable, recovered from the integrable exponential
  have hSmeas : AEMeasurable S P := by
    have h1 := hint.aestronglyMeasurable.aemeasurable
    have h2 : (fun y : ℝ => premium + Real.log y / nu) ∘
        (fun ω => Real.exp (-nu * riskSurplus arrival claims premium 0 1 ω)) = S := by
      funext ω
      simp only [Function.comp, Real.log_exp, hR]
      field_simp
      ring
    rw [← h2]
    exact (by fun_prop : Measurable fun y : ℝ => premium + Real.log y / nu).comp_aemeasurable h1
  -- integrability of exp(ν S)
  have hintS : Integrable (fun ω => Real.exp (nu * S ω)) P := by
    have := hint.const_mul (Real.exp (nu * premium))
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp only [hexpR, ← mul_assoc, ← Real.exp_add]
    ring_nf
  -- the explicit compound Poisson law
  set r : ℝ := (rate : ℝ) with hr
  set w : ℕ → ℝ := fun n => Real.exp (-r) * r ^ n / (n.factorial : ℝ) with hw
  have hw_nonneg : ∀ n, 0 ≤ w n := fun n => by positivity
  have hw_sum : HasSum w 1 := hasSum_one_poissonMeasure rate
  set Q : Measure ℝ := Measure.sum (fun n => ENNReal.ofReal (w n) • convPow F n) with hQ
  haveI : IsProbabilityMeasure Q := by
    constructor
    rw [hQ, Measure.sum_apply _ MeasurableSet.univ]
    simp only [Measure.smul_apply, measure_univ, smul_eq_mul, mul_one]
    haveI := lre_convPow_isProb F
    simp only [measure_univ, mul_one]
    rw [← ENNReal.ofReal_tsum_of_nonneg hw_nonneg hw_sum.summable, hw_sum.tsum_eq,
      ENNReal.ofReal_one]
  haveI : IsProbabilityMeasure (P.map S) := Measure.isProbabilityMeasure_map hSmeas
  -- characteristic function of Q
  have hcfQ : ∀ t : ℝ, charFun Q t =
      Complex.exp (r * (charFun F t - 1)) := by
    intro t
    have hintQ : Integrable (fun x : ℝ => Complex.exp (↑(inner ℝ x t) * Complex.I)) Q :=
      (integrable_const (1 : ℝ)).mono (by fun_prop) (Filter.Eventually.of_forall fun a => by
        have : (↑(inner ℝ a t) * Complex.I) = ((a * t : ℝ) : ℂ) * Complex.I := by
          simp [Real.inner_apply, mul_comm]
        rw [this, Complex.norm_exp_ofReal_mul_I]; simp)
    rw [charFun_apply, hQ, integral_sum_measure hintQ]
    simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hw_nonneg _)]
    have hterm : ∀ n, (w n) • ∫ x, Complex.exp (↑(inner ℝ x t) * Complex.I) ∂(convPow F n) =
        (Real.exp (-r) : ℂ) * (((r : ℂ) * charFun F t) ^ n / (n.factorial : ℂ)) := by
      intro n
      rw [← charFun_apply, lre_charFun_convPow F t n, hw]
      rw [Complex.real_smul]
      push_cast
      rw [mul_pow]
      ring
    simp_rw [hterm]
    rw [tsum_mul_left,
      (NormedSpace.expSeries_div_hasSum_exp ((r : ℂ) * charFun F t)).tsum_eq,
      ← Complex.exp_eq_exp_ℂ, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  -- characteristic function of S
  have hcfS : ∀ t : ℝ, charFun (P.map S) t = Complex.exp (r * (charFun F t - 1)) := by
    intro t
    have hF0 : F {0} = 0 := measure_mono_null (by simp) hclaimpos
    have := Kyprianou.Ch01.compoundPoissonCharExponent P F arrival claims rate hd hrate hF0
      0 1 t
    rw [hS, this]
    congr 1
    push_cast
    ring
  have hlaw : P.map S = Q := Measure.ext_of_charFun (funext fun t => by rw [hcfS, hcfQ])
  -- exponential moment of Q
  set M : ℝ≥0∞ := ∫⁻ x, ENNReal.ofReal (Real.exp (nu * x)) ∂F with hM
  have hlintQ : ∫⁻ x, ENNReal.ofReal (Real.exp (nu * x)) ∂Q =
      ∑' n, ENNReal.ofReal (w n) * M ^ n := by
    rw [hQ, lintegral_sum_measure]
    congr 1; funext n
    rw [lintegral_smul_measure, lre_lintegral_exp_convPow F nu n]
    rfl
  have hlintP : ∫⁻ ω, ENNReal.ofReal (Real.exp (nu * S ω)) ∂P =
      ∫⁻ x, ENNReal.ofReal (Real.exp (nu * x)) ∂Q := by
    rw [← hlaw, lintegral_map' (by fun_prop) hSmeas]
  have hfinP : ∫⁻ ω, ENNReal.ofReal (Real.exp (nu * S ω)) ∂P ≠ ⊤ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hintS
      (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le)]
    exact ENNReal.ofReal_ne_top
  have hMfin : M ≠ ⊤ := by
    intro hMtop
    apply hfinP
    rw [hlintP, hlintQ]
    have hle := ENNReal.le_tsum (f := fun n => ENNReal.ofReal (w n) * M ^ n) 1
    have hw1 : 0 < w 1 := by simp only [hw]; positivity
    have : ENNReal.ofReal (w 1) * M ^ 1 = ⊤ := by
      rw [pow_one, hMtop, ENNReal.mul_top (by simpa using hw1)]
    rw [this] at hle
    exact top_le_iff.mp hle
  -- integrability of exp(ν x) under F
  have hintF : Integrable (fun x : ℝ => Real.exp (nu * x)) F := by
    refine ⟨by fun_prop, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
    exact lt_top_iff_ne_top.mpr hMfin
  refine ⟨hintF, ?_⟩
  set m : ℝ := ∫ x, Real.exp (nu * x) ∂F with hm
  have hMm : M = ENNReal.ofReal m := by
    rw [hm, ofReal_integral_eq_lintegral_ofReal hintF
      (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le)]
  have hm_nonneg : 0 ≤ m := integral_nonneg fun x => (Real.exp_pos _).le
  -- the real exponential moment of S
  have hseries : HasSum (fun n => w n * m ^ n) (Real.exp (-r) * Real.exp (r * m)) := by
    have h := (NormedSpace.expSeries_div_hasSum_exp (r * m)).mul_left (Real.exp (-r))
    rw [← Real.exp_eq_exp_ℝ] at h
    refine h.congr_fun ?_
    intro n
    simp only [hw, mul_pow]
    ring
  have hES : ∫ ω, Real.exp (nu * S ω) ∂P = Real.exp (-r) * Real.exp (r * m) := by
    have h1 : ENNReal.ofReal (∫ ω, Real.exp (nu * S ω) ∂P) =
        ENNReal.ofReal (Real.exp (-r) * Real.exp (r * m)) := by
      rw [ofReal_integral_eq_lintegral_ofReal hintS
        (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), hlintP, hlintQ, hMm,
        ← hseries.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun n => mul_nonneg (hw_nonneg n) (pow_nonneg hm_nonneg n))
          hseries.summable]
      congr 1; funext n
      rw [ENNReal.ofReal_mul (hw_nonneg n), ENNReal.ofReal_pow hm_nonneg]
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun ω => (Real.exp_pos _).le)
      (by positivity)).mp h1
  -- use the root equation
  have hroot' : Real.exp (-nu * premium) * (Real.exp (-r) * Real.exp (r * m)) = 1 := by
    rw [← hES, ← integral_const_mul, ← hroot]
    congr 1; funext ω; rw [hexpR]
  have hexp0 : Real.exp (-nu * premium + -r + r * m) = 1 := by
    rw [Real.exp_add, Real.exp_add, mul_assoc]; exact hroot'
  have hlin : -nu * premium + -r + r * m = 0 := Real.exp_eq_one_iff _ |>.mp hexp0
  have hsub : ∫ x, (Real.exp (nu * x) - 1) ∂F = m - 1 := by
    rw [integral_sub hintF (integrable_const _), integral_const, hm]
    simp
  rw [hsub]
  linarith
