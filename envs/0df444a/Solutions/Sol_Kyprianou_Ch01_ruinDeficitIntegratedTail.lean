-- Prove2me | solution 1 for Kyprianou.Ch01.ruinDeficitIntegratedTail
-- status  : ACCEPTED   (prove)
-- author  : @doctosil
-- created : 2026-11-21T17:50:07.455949+00:00
-- url     : https://prove2.me/submissions/4371d26e-cf66-41e0-8599-5ae260a66729

import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_LeanLevy_Processes_CompoundPoisson
import Theorems.Thm_Kyprianou_Ch01_integratedTailLaw_exists
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_interarrival_pos
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_strictMono_arrival
import Theorems.Thm_ProbabilityTheory_IsCompoundPoissonDriver_ae_tendsto_arrival
import Theorems.Thm_ProbabilityTheory_lt_jumpCount_iff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.StrongLaw
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal BigOperators Topology
set_option autoImplicit false
universe u

private lemma integrable_id_expMeasure_rd {r : ℝ} (hr : 0 < r) :
    Integrable (fun x : ℝ => x) (expMeasure r) := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hlt : ∀ᵐ x ∂volume, gammaPDF 1 r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integrable_withDensity_iff hmeas hlt]
  have hEq : (fun x : ℝ => x * (gammaPDF 1 r x).toReal) =
      (Set.Ici (0 : ℝ)).indicator (fun x : ℝ => r * (x * Real.exp (-(r * x)))) := by
    ext x
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
      simp only [gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx),
        gammaPDF_of_neg (lt_of_not_ge hx)]
      simp
  rw [hEq, integrable_indicator_iff measurableSet_Ici, integrableOn_Ici_iff_integrableOn_Ioi]
  have hDom : IntegrableOn (fun x : ℝ => (2 : ℝ) * Real.exp (-(r / 2) * x)) (Set.Ioi 0) volume :=
    (integrableOn_exp_mul_Ioi (by linarith : -(r / 2) < 0) 0).const_mul 2
  refine hDom.mono' ?_ ?_
  · exact (measurable_const.mul (measurable_id.mul
      (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id).neg))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := hx
    rw [Real.norm_of_nonneg (by positivity)]
    have h1 : (r / 2) * x ≤ Real.exp ((r / 2) * x) := by
      linarith [Real.add_one_le_exp ((r / 2) * x)]
    have h2 : r * x * Real.exp (-(r * x)) ≤ 2 * Real.exp (-(r / 2) * x) := by
      have hmul : 2 * ((r / 2) * x) * Real.exp (-(r * x)) ≤
          2 * Real.exp ((r / 2) * x) * Real.exp (-(r * x)) := by
        gcongr
      calc r * x * Real.exp (-(r * x))
          = 2 * ((r / 2) * x) * Real.exp (-(r * x)) := by ring
        _ ≤ 2 * Real.exp ((r / 2) * x) * Real.exp (-(r * x)) := hmul
        _ = 2 * (Real.exp ((r / 2) * x) * Real.exp (-(r * x))) := by ring
        _ = 2 * Real.exp ((r / 2) * x + -(r * x)) := by rw [← Real.exp_add]
        _ = 2 * Real.exp (-(r / 2) * x) := by congr 2; ring
    linarith

private lemma integral_id_expMeasure_rd {r : ℝ} (hr : 0 < r) :
    (∫ x, x ∂(expMeasure r)) = 1 / r := by
  have hmeas : Measurable (gammaPDF 1 r) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 r)
  have hlt : ∀ᵐ x ∂volume, gammaPDF 1 r x < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  have hEq : (fun x : ℝ => (gammaPDF 1 r x).toReal • x) =
      (Set.Ici (0 : ℝ)).indicator (fun x : ℝ => r * (x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)))) := by
    ext x
    by_cases hx : 0 ≤ x
    · rw [Set.indicator_of_mem (show x ∈ Set.Ici (0 : ℝ) from hx)]
      simp only [smul_eq_mul, gammaPDF, gammaPDFReal, if_pos hx, Real.rpow_one, Real.Gamma_one,
        div_one, sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
      have h21 : (2 : ℝ) - 1 = 1 := by norm_num
      rw [h21, Real.rpow_one]
      ring
    · rw [Set.indicator_of_notMem (show x ∉ Set.Ici (0 : ℝ) from hx),
        gammaPDF_of_neg (lt_of_not_ge hx)]
      simp
  rw [hEq, integral_indicator measurableSet_Ici, integral_Ici_eq_integral_Ioi, integral_const_mul]
  have hInt : (∫ x in Set.Ioi (0 : ℝ), x ^ ((2 : ℝ) - 1) * Real.exp (-(r * x)) ∂volume) =
      (1 / r) ^ (2 : ℝ) * Real.Gamma 2 := by
    simpa [neg_mul] using
      (Real.integral_rpow_mul_exp_neg_mul_Ioi (by norm_num : (0 : ℝ) < 2) hr)
  rw [hInt]
  have hG2 : Real.Gamma 2 = 1 := by
    rw [show (2 : ℝ) = (1 : ℕ) + 1 by norm_num, Real.Gamma_nat_eq_factorial]
    simp
  rw [hG2, mul_one, show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  field_simp [hr.ne']

private lemma expMeasure_map_mul_rd {r c : ℝ} (hr : 0 < r) (hc : 0 < c) :
    (expMeasure r).map (fun x => c * x) = expMeasure (r / c) := by
  have hrc : 0 < r / c := div_pos hr hc
  have : IsProbabilityMeasure (expMeasure r) := isProbabilityMeasure_expMeasure hr
  have : IsProbabilityMeasure (expMeasure (r / c)) := isProbabilityMeasure_expMeasure hrc
  have : IsProbabilityMeasure ((expMeasure r).map (fun x => c * x)) :=
    Measure.isProbabilityMeasure_map (measurable_const_mul c).aemeasurable
  refine Measure.ext_of_Iic _ _ fun a => ?_
  rw [Measure.map_apply (measurable_const_mul c) measurableSet_Iic]
  have hpre : (fun x : ℝ => c * x) ⁻¹' Set.Iic a = Set.Iic (a / c) := by
    ext x; simp [Set.mem_preimage, Set.mem_Iic, le_div_iff₀ hc, mul_comm]
  rw [hpre]
  have h1 : ((expMeasure r) (Set.Iic (a / c))).toReal = cdf (expMeasure r) (a / c) := by
    rw [cdf_eq_real, Measure.real]
  have h2 : ((expMeasure (r / c)) (Set.Iic a)).toReal = cdf (expMeasure (r / c)) a := by
    rw [cdf_eq_real, Measure.real]
  have hcdf : cdf (expMeasure r) (a / c) = cdf (expMeasure (r / c)) a := by
    rw [cdf_expMeasure_eq hr, cdf_expMeasure_eq hrc]
    have hiff : (0 ≤ a / c) ↔ (0 ≤ a) := by rw [le_div_iff₀ hc, zero_mul]
    by_cases ha : 0 ≤ a
    · rw [if_pos (hiff.mpr ha), if_pos ha]; congr 2; field_simp [hc.ne']
    · rw [if_neg (mt hiff.mp ha), if_neg ha]
  have htoReal : ((expMeasure r) (Set.Iic (a / c))).toReal = ((expMeasure (r / c)) (Set.Iic a)).toReal := by
    rw [h1, h2, hcdf]
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp htoReal

private lemma expMeasure_lindley_charFun {γ ξ z : ℝ} (hγ : 0 < γ) (hz : 0 ≤ z) :
    (∫ t, Complex.exp (((ξ : ℂ) * ((max 0 (z - t) : ℝ) : ℂ)) * Complex.I) ∂(expMeasure γ)) =
      ((γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) +
        Complex.I * (ξ : ℂ) * ((Real.exp (-γ * z) : ℝ) : ℂ)) /
        ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
  have hden_ne : ((γ : ℂ) + Complex.I * (ξ : ℂ)) ≠ 0 := by
    intro h0
    have hre := congrArg Complex.re h0
    simp at hre
    linarith
  have hmeas : Measurable (gammaPDF 1 γ) :=
    ENNReal.measurable_ofReal.comp (measurable_gammaPDFReal 1 γ)
  have hlt : ∀ᵐ t ∂volume, gammaPDF 1 γ t < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [expMeasure, gammaMeasure, integral_withDensity_eq_integral_toReal_smul hmeas hlt]
  let f : ℝ → ℂ := fun t =>
    ((γ * Real.exp (-(γ * t)) : ℝ) : ℂ) *
      Complex.exp (((ξ : ℂ) * ((max 0 (z - t) : ℝ) : ℂ)) * Complex.I)
  have hEq : (fun t : ℝ => (gammaPDF 1 γ t).toReal •
      Complex.exp (((ξ : ℂ) * ((max 0 (z - t) : ℝ) : ℂ)) * Complex.I)) =
      (Set.Ici (0 : ℝ)).indicator f := by
    ext t
    by_cases ht : 0 ≤ t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ici (0 : ℝ) from ht), Complex.real_smul]
      simp only [f, gammaPDF, gammaPDFReal, if_pos ht, Real.rpow_one, Real.Gamma_one, div_one,
        sub_self, Real.rpow_zero, mul_one]
      rw [ENNReal.toReal_ofReal (by positivity)]
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ici (0 : ℝ) from ht),
        gammaPDF_of_neg (lt_of_not_ge ht)]
      simp
  rw [hEq, integral_indicator measurableSet_Ici, setIntegral_congr_set Ioi_ae_eq_Ici.symm]
  have hf_int : IntegrableOn f (Set.Ioi (0 : ℝ)) := by
    have hdom : IntegrableOn (fun t : ℝ => γ * Real.exp ((-γ) * t)) (Set.Ioi (0 : ℝ)) :=
      (integrableOn_exp_mul_Ioi (by linarith) (0 : ℝ)).const_mul γ
    refine hdom.mono' ?_ ?_
    · refine ((Complex.continuous_ofReal.measurable.comp
        (measurable_const.mul (Real.continuous_exp.measurable.comp
          (measurable_const.mul measurable_id).neg))).mul ?_).aestronglyMeasurable
      exact Complex.continuous_exp.measurable.comp
        ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (measurable_const.max (measurable_const.sub measurable_id)))).mul measurable_const)
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t _
      dsimp only [f]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg hγ.le (Real.exp_pos _).le)]
      have harg : ((ξ : ℂ) * ((max 0 (z - t) : ℝ) : ℂ)) * Complex.I =
          ((ξ * max 0 (z - t) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I, mul_one, neg_mul]
  have hsplit_set : Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) z ∪ Set.Ioi z := by
    ext t; simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioc]
    constructor
    · intro ht; by_cases htz : t ≤ z
      · exact Or.inl ⟨ht, htz⟩
      · exact Or.inr (lt_of_not_ge htz)
    · rintro (⟨ht, _⟩ | htz)
      · exact ht
      · linarith
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) z) (Set.Ioi z) :=
    Set.disjoint_left.mpr fun t h1 h2 => not_lt_of_ge h1.2 h2
  rw [hsplit_set, setIntegral_union hdisj measurableSet_Ioi
    (hf_int.mono_set (Set.Ioc_subset_Ioi_self))
    (hf_int.mono_set (Set.Ioi_subset_Ioi hz))]
  -- Part 1: integral on Ioc 0 z
  have hPart1 : (∫ t in Set.Ioc (0 : ℝ) z, f t ∂volume) =
      (γ : ℂ) * (Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) - ((Real.exp (-γ * z) : ℝ) : ℂ)) /
        ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
    rw [← intervalIntegral.integral_of_le hz]
    let C0 : ℂ := (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)
    let a : ℂ := -((γ : ℂ) + Complex.I * (ξ : ℂ))
    let F1 : ℝ → ℂ := fun t => (C0 / a) * Complex.exp (a * (t : ℂ))
    have hDeriv : ∀ t ∈ Set.uIcc (0 : ℝ) z, HasDerivAt F1 (C0 * Complex.exp (a * (t : ℂ))) t := by
      intro t _
      have h1 : HasDerivAt (fun s : ℝ => a * (s : ℂ)) a t := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := t)).const_mul a
      have h2 := h1.cexp.const_mul (C0 / a)
      have ha_ne : a ≠ 0 := neg_ne_zero.mpr hden_ne
      have hval : (C0 / a) * (Complex.exp (a * (t : ℂ)) * a) = C0 * Complex.exp (a * (t : ℂ)) := by
        rw [mul_comm (Complex.exp (a * (t : ℂ))) a, ← mul_assoc, div_mul_cancel₀ _ ha_ne]
      simpa only [hval] using h2
    have hEq_int : Set.EqOn f (fun t => C0 * Complex.exp (a * (t : ℂ))) (Set.Ioc (0 : ℝ) z) := by
      intro t ht
      have htz : t ≤ z := ht.2
      dsimp only [f, C0, a]
      rw [max_eq_right (sub_nonneg.mpr htz)]
      rw [Complex.ofReal_mul, Complex.ofReal_exp, mul_assoc (γ : ℂ), ← Complex.exp_add,
        mul_assoc (γ : ℂ), ← Complex.exp_add]
      congr 1; congr 1
      push_cast; ring
    have hInt_g : IntervalIntegrable (fun t => C0 * Complex.exp (a * (t : ℂ))) volume 0 z :=
      (Continuous.intervalIntegrable
        (continuous_const.mul (Complex.continuous_exp.comp
          (continuous_const.mul Complex.continuous_ofReal))) 0 z)
    have hIntEq : (∫ t in (0 : ℝ)..z, f t) = ∫ t in (0 : ℝ)..z, C0 * Complex.exp (a * (t : ℂ)) :=
      intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht => by
        rw [Set.uIoc_of_le hz] at ht; exact hEq_int ht)
    rw [hIntEq, intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hInt_g]
    dsimp only [F1, C0, a]
    have hExp_z : Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) *
        Complex.exp (-((γ : ℂ) + Complex.I * (ξ : ℂ)) * (z : ℂ)) =
        ((Real.exp (-γ * z) : ℝ) : ℂ) := by
      rw [← Complex.exp_add, Complex.ofReal_exp]
      congr 1; push_cast; ring
    have ha_ne : -((γ : ℂ) + Complex.I * (ξ : ℂ)) ≠ 0 := neg_ne_zero.mpr hden_ne
    calc (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) *
            Complex.exp (-((γ : ℂ) + Complex.I * (ξ : ℂ)) * (z : ℂ)) -
          (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) *
            Complex.exp (-((γ : ℂ) + Complex.I * (ξ : ℂ)) * (0 : ℂ))
        = (γ : ℂ) * (Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) *
            Complex.exp (-((γ : ℂ) + Complex.I * (ξ : ℂ)) * (z : ℂ))) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) -
          (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
          simp [mul_zero, Complex.exp_zero]; ring
      _ = (γ : ℂ) * ((Real.exp (-γ * z) : ℝ) : ℂ) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) -
          (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) / -((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
          rw [hExp_z]
      _ = (γ : ℂ) * (Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) - ((Real.exp (-γ * z) : ℝ) : ℂ)) /
          ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
          field_simp [hden_ne, ha_ne]; ring
  -- Part 2: integral on Ioi z
  have hPart2 : (∫ t in Set.Ioi z, f t ∂volume) = ((Real.exp (-γ * z) : ℝ) : ℂ) := by
    have hEq2 : Set.EqOn f (fun t => ((γ * Real.exp ((-γ) * t) : ℝ) : ℂ)) (Set.Ioi z) := by
      intro t ht
      have hzt : z < t := ht
      dsimp only [f]
      rw [max_eq_left (by linarith : z - t ≤ 0)]
      simp [neg_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hEq2]
    have hof : (∫ t in Set.Ioi z, ((γ * Real.exp ((-γ) * t) : ℝ) : ℂ) ∂volume) =
        ((∫ t in Set.Ioi z, γ * Real.exp ((-γ) * t) ∂volume : ℝ) : ℂ) := integral_ofReal
    rw [hof, integral_const_mul, integral_exp_mul_Ioi (by linarith) z]
    congr 1
    field_simp [hγ.ne']
  rw [hPart1, hPart2, div_add' _ _ _ hden_ne]
  congr 1
  ring

private lemma integratedTail_eq_withDensity
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x → (eta (Set.Iic x)).toReal = integratedTailCDF F mu x) :
    eta = (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal)) := by
  let ν : Measure ℝ := (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
    (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal))
  have hdens_meas : Measurable (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal)) := by
    have hanti : Antitone (fun y : ℝ => (F (Set.Ioi y)).toReal) := fun a b hab =>
      ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Ioi_subset_Ioi hab))
    exact ENNReal.measurable_ofReal.comp (measurable_const.mul hanti.measurable)
  have hν_Iic : ∀ x : ℝ, ν (Set.Iic x) = eta (Set.Iic x) := by
    intro x
    by_cases hx : 0 ≤ x
    · have h1 : ν (Set.Iic x) =
          ∫⁻ y in Set.Ioc (0 : ℝ) x, ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal) ∂volume := by
        dsimp only [ν]
        rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hSet : Set.Iic x ∩ Set.Ioi (0 : ℝ) = Set.Ioc (0 : ℝ) x := by
          ext y; simp [Set.mem_Ioc, Set.mem_Iic, Set.mem_Ioi, and_comm]
        rw [hSet]
      have hint_Ioc : IntegrableOn (fun y : ℝ => (1 / mu) * (F (Set.Ioi y)).toReal)
          (Set.Ioc (0 : ℝ) x) := by
        have hanti : Antitone (fun y : ℝ => (F (Set.Ioi y)).toReal) := fun a b hab =>
          ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Ioi_subset_Ioi hab))
        refine (integrableOn_const (C := 1 / mu) (hs := measure_Ioc_lt_top.ne)).mono'
          ((measurable_const.mul hanti.measurable).aestronglyMeasurable) ?_
        filter_upwards with y
        have h0 : 0 ≤ (F (Set.Ioi y)).toReal := ENNReal.toReal_nonneg
        have hle1 : (F (Set.Ioi y)).toReal ≤ 1 :=
          ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one (μ := F) (s := Set.Ioi y))
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) h0)]
        nlinarith [div_pos one_pos hmu]
      have hnonneg : ∀ y : ℝ, 0 ≤ (1 / mu) * (F (Set.Ioi y)).toReal := fun y =>
        mul_nonneg (by positivity) ENNReal.toReal_nonneg
      rw [h1, ← ofReal_integral_eq_lintegral_ofReal hint_Ioc (Filter.Eventually.of_forall hnonneg),
        integral_const_mul]
      change ENNReal.ofReal (integratedTailCDF F mu x) = eta (Set.Iic x)
      rw [← heta x hx, ENNReal.ofReal_toReal (measure_ne_top eta _)]
    · have hlt : x < 0 := lt_of_not_ge hx
      have hν0 : ν (Set.Iic x) = 0 := by
        dsimp only [ν]
        rw [withDensity_apply _ measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic]
        have hemp : Set.Iic x ∩ Set.Ioi (0 : ℝ) = ∅ := by
          ext y; simp only [Set.mem_inter_iff, Set.mem_Iic, Set.mem_Ioi, Set.mem_empty_iff_false, iff_false]
          intro ⟨h1, h2⟩; linarith
        rw [hemp, Measure.restrict_empty, lintegral_zero_measure]
      have heta0 : eta (Set.Iic x) = 0 :=
        measure_mono_null (fun y hy => lt_of_le_of_lt hy hlt) hetaSupport
      rw [hν0, heta0]
  have hν_prob : IsProbabilityMeasure ν := by
    refine ⟨?_⟩
    have hUnion : (Set.univ : Set ℝ) = ⋃ n : ℕ, Set.Iic (n : ℝ) := by
      ext x; simp only [Set.mem_univ, Set.mem_iUnion, Set.mem_Iic, true_iff]
      exact exists_nat_ge x
    have hMono : Monotone (fun n : ℕ => Set.Iic (n : ℝ)) := fun m n hmn y hy =>
      Set.mem_Iic.mpr (le_trans (Set.mem_Iic.mp hy) (Nat.cast_le.mpr hmn))
    have h1 := tendsto_measure_iUnion_atTop (μ := ν) hMono
    have h2 := tendsto_measure_iUnion_atTop (μ := eta) hMono
    rw [← hUnion] at h1 h2
    have hEq_seq : (⇑ν ∘ fun n : ℕ => Set.Iic (n : ℝ)) = (⇑eta ∘ fun n : ℕ => Set.Iic (n : ℝ)) :=
      funext fun n => hν_Iic n
    rw [hEq_seq] at h1
    rw [tendsto_nhds_unique h1 h2, measure_univ]
  exact (Measure.ext_of_Iic ν eta hν_Iic).symm

private lemma integratedTail_charFun
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (eta : Measure ℝ) [IsProbabilityMeasure eta]
    (hetaSupport : eta (Set.Iio (0 : ℝ)) = 0)
    (heta : ∀ x : ℝ, 0 ≤ x → (eta (Set.Iic x)).toReal = integratedTailCDF F mu x)
    (ξ : ℝ) (hξ : ξ ≠ 0) :
    charFun eta ξ = (charFun F ξ - 1) / ((ξ : ℂ) * Complex.I * (mu : ℂ)) := by
  have heta_eq := integratedTail_eq_withDensity F mu hmu hclaimpos hclaimint hmean eta hetaSupport heta
  rw [charFun_apply_real, heta_eq]
  have hanti : Antitone (fun y : ℝ => (F (Set.Ioi y)).toReal) := fun a b hab =>
    ENNReal.toReal_mono (measure_ne_top F _) (measure_mono (Set.Ioi_subset_Ioi hab))
  have hfm : Measurable (fun y : ℝ => ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal)) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul hanti.measurable)
  have hflt : ∀ᵐ y ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal) < ⊤ :=
    Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top
  rw [integral_withDensity_eq_integral_toReal_smul hfm hflt]
  have hEq1 : ∀ y : ℝ,
      (ENNReal.ofReal ((1 / mu) * (F (Set.Ioi y)).toReal)).toReal •
        Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) =
      ((1 / mu : ℝ) : ℂ) * ∫ z, (if y < z then Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) else 0) ∂F := by
    intro y
    have hnn : 0 ≤ (1 / mu) * (F (Set.Ioi y)).toReal :=
      mul_nonneg (by positivity) ENNReal.toReal_nonneg
    rw [ENNReal.toReal_ofReal hnn, Complex.real_smul]
    have hInd : (fun z : ℝ => if y < z then Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) else 0) =
        (Set.Ioi y).indicator (fun _ => Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I)) := by
      ext z; by_cases h : y < z
      · simp [h, Set.indicator_of_mem (show z ∈ Set.Ioi y from h)]
      · simp [h, Set.indicator_of_notMem (show z ∉ Set.Ioi y from h)]
    rw [hInd, integral_indicator measurableSet_Ioi, setIntegral_const, Measure.real,
      Complex.real_smul]
    push_cast; ring
  simp_rw [hEq1]
  rw [integral_const_mul]
  -- Fubini swap on (volume.restrict (Ioi 0)).prod F
  let G : ℝ × ℝ → ℂ := fun p =>
    if p.1 < p.2 then Complex.exp ((ξ : ℂ) * (p.1 : ℂ) * Complex.I) else 0
  have hG_int : Integrable G ((volume.restrict (Set.Ioi (0 : ℝ))).prod F) := by
    have hG_meas : Measurable G :=
      Measurable.ite (measurableSet_lt measurable_fst measurable_snd)
        (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp measurable_fst)).mul
            measurable_const))
        measurable_const
    refine ⟨hG_meas.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    rw [lintegral_prod _ hG_meas.enorm.aemeasurable]
    have hSwap : ∫⁻ y in Set.Ioi (0 : ℝ), ∫⁻ z, ‖G (y, z)‖ₑ ∂F ∂volume =
        ∫⁻ z, ∫⁻ y in Set.Ioi (0 : ℝ), ‖G (y, z)‖ₑ ∂volume ∂F :=
      lintegral_lintegral_swap hG_meas.enorm.aemeasurable
    rw [hSwap]
    have hF_pos : ∀ᵐ z ∂F, 0 < z := by
      rw [ae_iff]; convert hclaimpos using 2; ext z; simp [not_lt]
    have hInner : ∀ᵐ z ∂F, (∫⁻ y in Set.Ioi (0 : ℝ), ‖G (y, z)‖ₑ ∂volume) = ENNReal.ofReal z := by
      filter_upwards [hF_pos] with z hz
      have hEq_n : ∀ y : ℝ, ‖G (y, z)‖ₑ = (Set.Iio z).indicator (fun _ => (1 : ℝ≥0∞)) y := by
        intro y
        by_cases h : y < z
        · have hm : y ∈ Set.Iio z := h
          rw [Set.indicator_of_mem hm]
          dsimp only [G]; rw [if_pos h]
          have harg : (ξ : ℂ) * (y : ℂ) * Complex.I = ((ξ * y : ℝ) : ℂ) * Complex.I := by
            push_cast; ring
          rw [harg, ← ofReal_norm, Complex.norm_exp_ofReal_mul_I, ENNReal.ofReal_one]
        · have hm : y ∉ Set.Iio z := h
          rw [Set.indicator_of_notMem hm]
          dsimp only [G]; rw [if_neg h]; simp
      simp_rw [hEq_n]
      rw [lintegral_indicator measurableSet_Iio, Measure.restrict_restrict measurableSet_Iio,
        lintegral_const, one_mul]
      have hSet : Set.Iio z ∩ Set.Ioi (0 : ℝ) = Set.Ioo (0 : ℝ) z := by
        ext y; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi, and_comm]
      rw [hSet, Measure.restrict_apply_univ, Real.volume_Ioo, sub_zero]
    rw [lintegral_congr_ae hInner]
    have hOfReal := ofReal_integral_eq_lintegral_ofReal hclaimint (hF_pos.mono fun _ hz => hz.le)
    rw [← hOfReal, hmean]
    exact ENNReal.ofReal_lt_top
  have hSwapInt := integral_integral_swap (f := fun y z => G (y, z)) hG_int
  change ((1 / mu : ℝ) : ℂ) * (∫ y in Set.Ioi (0 : ℝ), ∫ z, G (y, z) ∂F ∂volume) = _
  rw [hSwapInt]
  have hF_pos : ∀ᵐ z ∂F, 0 < z := by
    rw [ae_iff]; convert hclaimpos using 2; ext z; simp [not_lt]
  have hInnerInt : ∀ᵐ z ∂F,
      (∫ y in Set.Ioi (0 : ℝ), G (y, z) ∂volume) =
        (Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) - 1) / ((ξ : ℂ) * Complex.I) := by
    filter_upwards [hF_pos] with z hz
    have hInd : (fun y : ℝ => G (y, z)) =
        (Set.Iio z).indicator (fun y => Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I)) := by
      ext y; by_cases h : y < z
      · simp [G, h, Set.indicator_of_mem (show y ∈ Set.Iio z from h)]
      · simp [G, h, Set.indicator_of_notMem (show y ∉ Set.Iio z from h)]
    rw [hInd, setIntegral_indicator measurableSet_Iio]
    have hSet : Set.Ioi (0 : ℝ) ∩ Set.Iio z = Set.Ioo (0 : ℝ) z := by
      ext y; simp [Set.mem_Ioo, Set.mem_Iio, Set.mem_Ioi]
    rw [hSet, setIntegral_congr_set Ioo_ae_eq_Ioc, ← intervalIntegral.integral_of_le hz.le]
    let a : ℂ := (ξ : ℂ) * Complex.I
    have ha_ne : a ≠ 0 := mul_ne_zero (by exact_mod_cast hξ) Complex.I_ne_zero
    have hDeriv : ∀ y ∈ Set.uIcc (0 : ℝ) z,
        HasDerivAt (fun t : ℝ => Complex.exp ((ξ : ℂ) * (t : ℂ) * Complex.I) / a)
          (Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I)) y := by
      intro y _
      have h1 : HasDerivAt (fun t : ℝ => (ξ : ℂ) * (t : ℂ) * Complex.I) a y := by
        have h0 : (fun t : ℝ => (ξ : ℂ) * (t : ℂ) * Complex.I) = fun t : ℝ => a * (t : ℂ) := by
          ext t; dsimp only [a]; ring
        rw [h0]
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).const_mul a
      have h2 := h1.cexp.div_const a
      have hval : Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) * a / a =
          Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) := mul_div_cancel_right₀ _ ha_ne
      simpa only [hval] using h2
    have hIntCont : IntervalIntegrable (fun y : ℝ => Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I))
        volume 0 z :=
      Continuous.intervalIntegrable
        (Complex.continuous_exp.comp
          ((continuous_const.mul Complex.continuous_ofReal).mul continuous_const)) 0 z
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hDeriv hIntCont]
    simp [a, mul_zero, Complex.exp_zero, sub_div]
  rw [integral_congr_ae hInnerInt, integral_div]
  have hIntExp : Integrable (fun z : ℝ => Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)) F := by
    refine (integrable_const (1 : ℝ)).mono' ?_ ?_
    · exact (Complex.continuous_exp.measurable.comp
        ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const)).aestronglyMeasurable
    · refine Filter.Eventually.of_forall fun z => ?_
      have harg : (ξ : ℂ) * (z : ℂ) * Complex.I = ((ξ * z : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
  rw [integral_sub hIntExp (integrable_const 1), integral_const, probReal_univ, one_smul,
    ← charFun_apply_real]
  have hmu_ne : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
  have hξI_ne : ((ξ : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hξ) Complex.I_ne_zero
  push_cast
  field_simp [hmu_ne, hξI_ne]

private lemma finset_sup'_range_succ {α : Type*} [LinearOrder α] (f : ℕ → α) (N : ℕ) :
    (Finset.range (N + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos (N + 1))⟩ f =
      max ((Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ f) (f (N + 1)) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ fun n hn => ?_
    have hle : n ≤ N + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
    rcases lt_or_eq_of_le hle with hlt | rfl
    · exact le_max_of_le_left (Finset.le_sup' f (Finset.mem_range.mpr hlt))
    · exact le_max_right _ _
  · refine max_le ?_ (Finset.le_sup' f (Finset.mem_range.mpr (Nat.lt_succ_self (N + 1))))
    refine Finset.sup'_le _ _ fun n hn =>
      Finset.le_sup' f (Finset.mem_range.mpr (Nat.lt_succ_of_lt (Finset.mem_range.mp hn)))

private lemma measurable_sum_of_space {α ι : Type*} (m : MeasurableSpace α)
    (s : Finset ι) (f : ι → α → ℝ) (hf : ∀ i ∈ s, @Measurable α ℝ m _ (f i)) :
    @Measurable α ℝ m _ (fun ω => ∑ i ∈ s, f i ω) :=
  letI := m; Finset.measurable_sum s hf

private lemma measurable_iSup_ennreal_of_space {α : Type*} (m : MeasurableSpace α)
    (f : ℕ → α → ℝ≥0∞) (hf : ∀ n, @Measurable α ℝ≥0∞ m _ (f n)) :
    @Measurable α ℝ≥0∞ m _ (fun ω => ⨆ n, f n ω) :=
  letI := m; Measurable.iSup hf

private lemma measurableSet_le_const_of_space {α : Type*} (m : MeasurableSpace α)
    (f : α → ℝ) (c : ℝ) (hf : @Measurable α ℝ m _ f) :
    MeasurableSet[m] {ω | f ω ≤ c} :=
  letI := m; measurableSet_le hf measurable_const

private lemma measurableSet_const_lt_of_space {α : Type*} (m : MeasurableSpace α)
    (c : ℝ) (f : α → ℝ) (hf : @Measurable α ℝ m _ f) :
    MeasurableSet[m] {ω | c < f ω} :=
  letI := m; measurableSet_lt measurable_const hf

private lemma measurableSet_biInter_finset_of_space {α ι : Type*} (m : MeasurableSpace α)
    (s : Finset ι) (f : ι → Set α) (hf : ∀ i ∈ s, MeasurableSet[m] (f i)) :
    MeasurableSet[m] (⋂ i ∈ s, f i) :=
  letI := m; MeasurableSet.biInter (Finset.countable_toSet s) hf

private lemma measurable_sub_const_mul_of_space {α : Type*} (m : MeasurableSpace α)
    (c : ℝ) (f g : α → ℝ) (hf : @Measurable α ℝ m _ f) (hg : @Measurable α ℝ m _ g) :
    @Measurable α ℝ m _ (fun ω => f ω - c * g ω) :=
  letI := m; hf.sub (measurable_const.mul hg)

theorem solution
    {Ω : Type u} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (arrival claims : ℕ → Ω → ℝ) (rate : ℝ≥0)
    (F : Measure ℝ) [IsProbabilityMeasure F]
    (hd : IsCompoundPoissonDriver arrival claims rate F P)
    (hrate : 0 < rate)
    (mu : ℝ) (hmu : 0 < mu)
    (hclaimpos : F (Set.Iic (0 : ℝ)) = 0)
    (hclaimint : Integrable (fun x : ℝ => x) F)
    (hmean : (∫ x, x ∂F) = mu)
    (premium : ℝ) (hpremium : 0 < premium)
    (hnet : (rate : ℝ) * mu < premium) :
    ruinProbability P arrival claims premium 0 =
        (rate : ℝ) * mu / premium ∧
      ∀ x : ℝ, 0 ≤ x →
        (P (ruinEvent arrival claims premium 0 ∩
          {ω | ruinDeficit arrival claims premium 0 ω ≤ x})).toReal =
          ruinProbability P arrival claims premium 0 *
            integratedTailCDF F mu x := by
  have hrateR : (0 : ℝ) < (rate : ℝ) := NNReal.coe_pos.mpr hrate
  set γ : ℝ := (rate : ℝ) / premium
  have hγ : 0 < γ := div_pos hrateR hpremium
  set ρ : ℝ := (rate : ℝ) * mu / premium
  have hρ_pos : 0 < ρ := div_pos (mul_pos hrateR hmu) hpremium
  have hρ_lt1 : ρ < 1 := (div_lt_one hpremium).mpr hnet
  -- Obtain integrated-tail probability measure eta
  obtain ⟨eta, hetaProb, hetaSupp, hetaCDF⟩ :=
    Kyprianou.Ch01.integratedTailLaw_exists F mu hmu hclaimpos hclaimint hmean
  -- Step 1: Discrete random walk Z i = claims i - premium * arrival i and shifted suprema M_from k
  let Z : ℕ → Ω → ℝ := fun i ω => claims i ω - premium * arrival i ω
  have hZ_meas : ∀ i, Measurable (Z i) := fun i =>
    (hd.measurable_mark i).sub (measurable_const.mul (hd.measurable_interarrival i))
  let S_from : ℕ → ℕ → Ω → ℝ := fun k n ω => ∑ i ∈ Finset.range n, Z (k + i) ω
  have hS_meas : ∀ k n, Measurable (S_from k n) := fun k n =>
    Finset.measurable_sum (Finset.range n) fun i _ => hZ_meas (k + i)
  let M_fin : ℕ → ℕ → Ω → ℝ := fun k N ω =>
    (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩ (fun n => S_from k n ω)
  have hM_fin_nonneg : ∀ k N ω, 0 ≤ M_fin k N ω := fun k N ω => by
    have h0 : S_from k 0 ω ≤ M_fin k N ω :=
      Finset.le_sup' (f := fun n => S_from k n ω) (Finset.mem_range.mpr (Nat.succ_pos N))
    simpa [S_from] using h0
  have hM_fin_meas : ∀ k N, Measurable (M_fin k N) := fun k N => by
    induction N with
    | zero =>
        have hEq : M_fin k 0 = fun _ => (0 : ℝ) := by ext ω; simp [M_fin, S_from]
        rw [hEq]; exact measurable_const
    | succ N ih =>
        have hEq : M_fin k (N + 1) = fun ω => max (M_fin k N ω) (S_from k (N + 1) ω) := by
          ext ω
          exact finset_sup'_range_succ (fun n => S_from k n ω) N
        rw [hEq]
        exact ih.max (hS_meas k (N + 1))
  let M_from : ℕ → Ω → ℝ := fun k ω => (⨆ N : ℕ, ENNReal.ofReal (M_fin k N ω)).toReal
  have hM_meas : ∀ k, Measurable (M_from k) := fun k =>
    ENNReal.measurable_toReal.comp (Measurable.iSup fun N => ENNReal.measurable_ofReal.comp (hM_fin_meas k N))
  have hM_nonneg : ∀ k ω, 0 ≤ M_from k ω := fun k ω => ENNReal.toReal_nonneg
  -- Step 2: Almost sure path properties & SLLN -> S_from k n → -∞
  have hArrPos := hd.ae_interarrival_pos hrate
  have hStrict := hd.ae_strictMono_arrival hrate
  have hTendsto := hd.ae_tendsto_arrival hrate
  have hClaimsPos : ∀ᵐ ω ∂P, ∀ n : ℕ, 0 < claims n ω := by
    rw [ae_all_iff]
    intro n
    have hzero : P {ω | claims n ω ≤ 0} = 0 := by
      have hpre : {ω | claims n ω ≤ 0} = claims n ⁻¹' Set.Iic (0 : ℝ) := rfl
      rw [hpre, ← Measure.map_apply (hd.measurable_mark n) measurableSet_Iic,
        (hd.law_mark n).map_eq, hclaimpos]
    rw [ae_iff]
    convert hzero using 2
    ext ω; simp [not_lt]
  have hS_tendsto_neg : ∀ᵐ ω ∂P, ∀ k : ℕ, Tendsto (fun n : ℕ => S_from k n ω) atTop atBot := by
    have hArr_iid : Pairwise (fun i j => IndepFun (arrival i) (arrival j) P) := fun i j hij =>
      hd.indep.indepFun (show (Sum.inl i : ℕ ⊕ ℕ) ≠ Sum.inl j by simp [hij])
    have hArr_ident : ∀ i, IdentDistrib (arrival i) (arrival 0) P P := fun i =>
      { aemeasurable_fst := (hd.measurable_interarrival i).aemeasurable
        aemeasurable_snd := (hd.measurable_interarrival 0).aemeasurable
        map_eq := by rw [(hd.law_interarrival i).map_eq, (hd.law_interarrival 0).map_eq] }
    have hArr_int : Integrable (arrival 0) P := by
      have h1 := integrable_id_expMeasure_rd hrateR
      rw [← (hd.law_interarrival 0).map_eq] at h1
      exact (integrable_map_measure h1.aestronglyMeasurable
        (hd.measurable_interarrival 0).aemeasurable).mp h1
    have hArr_mean : (∫ ω, arrival 0 ω ∂P) = 1 / (rate : ℝ) := by
      have hmap := integral_map (μ := P) (φ := arrival 0) (f := fun x : ℝ => x)
        (hd.measurable_interarrival 0).aemeasurable (by fun_prop)
      rw [← hmap, (hd.law_interarrival 0).map_eq]
      exact integral_id_expMeasure_rd hrateR
    have hSLLN_arr := ProbabilityTheory.strong_law_ae_real arrival hArr_int hArr_iid hArr_ident
    rw [hArr_mean] at hSLLN_arr
    have hClm_iid : Pairwise (fun i j => IndepFun (claims i) (claims j) P) := fun i j hij =>
      hd.indep.indepFun (show (Sum.inr i : ℕ ⊕ ℕ) ≠ Sum.inr j by simp [hij])
    have hClm_ident : ∀ i, IdentDistrib (claims i) (claims 0) P P := fun i =>
      { aemeasurable_fst := (hd.measurable_mark i).aemeasurable
        aemeasurable_snd := (hd.measurable_mark 0).aemeasurable
        map_eq := by rw [(hd.law_mark i).map_eq, (hd.law_mark 0).map_eq] }
    have hClm_int : Integrable (claims 0) P := by
      have h1 := hclaimint
      rw [← (hd.law_mark 0).map_eq] at h1
      exact (integrable_map_measure h1.aestronglyMeasurable
        (hd.measurable_mark 0).aemeasurable).mp h1
    have hClm_mean : (∫ ω, claims 0 ω ∂P) = mu := by
      have hmap := integral_map (μ := P) (φ := claims 0) (f := fun x : ℝ => x)
        (hd.measurable_mark 0).aemeasurable (by fun_prop)
      rw [← hmap, (hd.law_mark 0).map_eq]
      exact hmean
    have hSLLN_clm := ProbabilityTheory.strong_law_ae_real claims hClm_int hClm_iid hClm_ident
    rw [hClm_mean] at hSLLN_clm
    filter_upwards [hSLLN_arr, hSLLN_clm] with ω hArrω hClmω
    have hS0_div : Tendsto (fun n : ℕ => S_from 0 n ω / (n : ℝ)) atTop
        (𝓝 (mu - premium * (1 / (rate : ℝ)))) := by
      have hEq : (fun n : ℕ => S_from 0 n ω / (n : ℝ)) =
          fun n => (∑ i ∈ Finset.range n, claims i ω) / (n : ℝ) -
            premium * ((∑ i ∈ Finset.range n, arrival i ω) / (n : ℝ)) := by
        ext n
        dsimp only [S_from, Z]
        simp only [zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum]
        ring
      rw [hEq]
      exact hClmω.sub (hArrω.const_mul premium)
    have hdrift_neg : mu - premium * (1 / (rate : ℝ)) < 0 := by
      have : (rate : ℝ) * (mu - premium * (1 / (rate : ℝ))) = (rate : ℝ) * mu - premium := by
        field_simp [hrateR.ne']
      nlinarith
    have hS0_bot : Tendsto (fun n : ℕ => S_from 0 n ω) atTop atBot := by
      rw [tendsto_atBot]
      intro b
      rw [Filter.eventually_atTop]
      have hEv := hS0_div.eventually (gt_mem_nhds (by linarith :
        mu - premium * (1 / (rate : ℝ)) < (mu - premium * (1 / (rate : ℝ))) / 2))
      rw [Filter.eventually_atTop] at hEv
      obtain ⟨N1, hN1⟩ := hEv
      set d : ℝ := -(mu - premium * (1 / (rate : ℝ))) / 2
      have hd_pos : 0 < d := by dsimp [d]; linarith
      obtain ⟨N2, hN2⟩ := exists_nat_gt (max (-b / d) 1)
      refine ⟨max N1 N2, fun n hn => ?_⟩
      have hn1 : N1 ≤ n := le_trans (le_max_left _ _) hn
      have hn2 : N2 ≤ n := le_trans (le_max_right _ _) hn
      have hn_pos : (0 : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) < (N2 : ℝ) := lt_of_le_of_lt (le_max_right _ _) hN2
        have h2 : (N2 : ℝ) ≤ (n : ℝ) := Nat.cast_le.mpr hn2
        linarith
      have hdiv := hN1 n hn1
      have hmul : S_from 0 n ω < -d * (n : ℝ) := by
        have hlt : S_from 0 n ω / (n : ℝ) < -d := by dsimp [d]; linarith
        rwa [div_lt_iff₀ hn_pos] at hlt
      have hbd : -b / d < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) (lt_of_lt_of_le hN2 (Nat.cast_le.mpr hn2))
      have hbd2 : -b < (n : ℝ) * d := (div_lt_iff₀ hd_pos).mp hbd
      linarith
    intro k
    have hShift : (fun n : ℕ => S_from k n ω) = fun n => S_from 0 (n + k) ω - S_from 0 k ω := by
      ext n
      have hsum := Finset.sum_range_add (fun i => Z i ω) k n
      dsimp only [S_from]
      simp only [zero_add]
      rw [add_comm n k, hsum]
      ring
    rw [hShift]
    have hcomp : Tendsto (fun n : ℕ => S_from 0 (n + k) ω) atTop atBot :=
      hS0_bot.comp (tendsto_add_atTop_nat k)
    rw [tendsto_atBot] at hcomp ⊢
    intro b
    rw [Filter.eventually_atTop]
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hcomp (b + S_from 0 k ω))
    exact ⟨N, fun n hn => by linarith [hN n hn]⟩
  -- Step 3: Eventual constancy of M_fin k N → M_from k and pathwise identities
  have hM_ev_const : ∀ᵐ ω ∂P, ∀ k : ℕ, ∃ N0 : ℕ,
      (∀ N ≥ N0, M_fin k N ω = M_from k ω) ∧
      (∀ n : ℕ, S_from k n ω ≤ M_from k ω) ∧
      (∃ n ≤ N0, S_from k n ω = M_from k ω) := by
    filter_upwards [hS_tendsto_neg] with ω hBotω k
    have hBot_k := hBotω k
    rw [tendsto_atBot] at hBot_k
    obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp (hBot_k 0)
    have hConst : ∀ N ≥ N0, M_fin k N ω = M_fin k N0 ω := by
      intro N hN
      apply le_antisymm
      · refine Finset.sup'_le _ _ fun n hn => ?_
        by_cases hle : n ≤ N0
        · exact Finset.le_sup' (f := fun j => S_from k j ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
        · have hge : N0 ≤ n := le_of_not_ge hle
          exact le_trans (hN0 n hge) (hM_fin_nonneg k N0 ω)
      · refine Finset.sup'_le _ _ fun n hn => ?_
        have hlt : n < N0 + 1 := Finset.mem_range.mp hn
        exact Finset.le_sup' (f := fun j => S_from k j ω) (Finset.mem_range.mpr (by omega))
    have hMono : ∀ N : ℕ, M_fin k N ω ≤ M_fin k N0 ω := fun N => by
      by_cases hN : N0 ≤ N
      · rw [hConst N hN]
      · refine Finset.sup'_le _ _ fun n hn => ?_
        have hlt : n < N + 1 := Finset.mem_range.mp hn
        exact Finset.le_sup' (f := fun j => S_from k j ω) (Finset.mem_range.mpr (by omega))
    have hSup_eq : (⨆ N : ℕ, ENNReal.ofReal (M_fin k N ω)) = ENNReal.ofReal (M_fin k N0 ω) := by
      apply le_antisymm
      · exact iSup_le fun N => ENNReal.ofReal_le_ofReal (hMono N)
      · exact le_iSup (fun N => ENNReal.ofReal (M_fin k N ω)) N0
    have hM_eq : M_from k ω = M_fin k N0 ω := by
      dsimp only [M_from]
      rw [hSup_eq, ENNReal.toReal_ofReal (hM_fin_nonneg k N0 ω)]
    refine ⟨N0, fun N hN => by rw [hConst N hN, hM_eq], fun n => ?_, ?_⟩
    · rw [hM_eq]
      by_cases hle : n ≤ N0
      · exact Finset.le_sup' (f := fun j => S_from k j ω) (Finset.mem_range.mpr (Nat.lt_succ_of_le hle))
      · exact le_trans (hN0 n (le_of_not_ge hle)) (hM_fin_nonneg k N0 ω)
    · obtain ⟨n, hn, hmax⟩ := Finset.exists_mem_eq_sup'
        ⟨0, Finset.mem_range.mpr (Nat.succ_pos N0)⟩ (fun j => S_from k j ω)
      exact ⟨n, Nat.lt_succ_iff.mp (Finset.mem_range.mp hn), by rw [hM_eq]; exact hmax.symm⟩
  -- Step 4: Shift invariance P.map (M_from k) = P.map (M_from 0)
  have hM_law_eq : ∀ k : ℕ, P.map (M_from k) = P.map (M_from 0) := by
    intro k
    have hFin_law : ∀ N : ℕ, P.map (M_fin k N) = P.map (M_fin 0 N) := by
      intro N
      let emb : ℕ → Fin N ⊕ Fin N → ℕ ⊕ ℕ := fun m => Sum.map (fun i : Fin N => m + i.1) (fun i : Fin N => m + i.1)
      have hemb_inj : ∀ m, Function.Injective (emb m) := fun m =>
        Function.Injective.sumMap (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
          (fun _ _ h => Fin.ext (Nat.add_left_cancel h))
      let X_tup : ℕ → Ω → (Fin N ⊕ Fin N → ℝ) := fun m ω idx => Sum.elim arrival claims (emb m idx) ω
      have hX_meas : ∀ m (idx : Fin N ⊕ Fin N), Measurable (fun ω => X_tup m ω idx) := fun m idx => by
        cases idx with
        | inl i => exact hd.measurable_interarrival (m + i.1)
        | inr i => exact hd.measurable_mark (m + i.1)
      have hPi_law : ∀ m : ℕ, P.map (X_tup m) =
          Measure.pi (fun idx : Fin N ⊕ Fin N =>
            Sum.elim (fun _ : Fin N => expMeasure (rate : ℝ)) (fun _ : Fin N => F) idx) := fun m => by
        have hind : iIndepFun (fun idx : Fin N ⊕ Fin N => fun ω => X_tup m ω idx) P :=
          hd.indep.precomp (hemb_inj m)
        have hmap := (iIndepFun_iff_map_fun_eq_pi_map (fun idx => (hX_meas m idx).aemeasurable)).mp hind
        rw [hmap]
        congr 1; funext idx
        cases idx with
        | inl i => exact (hd.law_interarrival (m + i.1)).map_eq
        | inr i => exact (hd.law_mark (m + i.1)).map_eq
      let Ψ : (Fin N ⊕ Fin N → ℝ) → ℝ := fun v =>
        (Finset.range (N + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos N)⟩
          (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0)
      have hΨ_meas : Measurable Ψ := by
        have hterm : ∀ n : ℕ, Measurable (fun v : Fin N ⊕ Fin N → ℝ =>
            ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0) := fun n =>
          Finset.measurable_sum Finset.univ fun i _ => by
            by_cases h : i.1 < n
            · simp only [if_pos h]
              exact (measurable_pi_apply _).sub (measurable_const.mul (measurable_pi_apply _))
            · simp only [if_neg h]; exact measurable_const
        have haux : ∀ m : ℕ, Measurable (fun v : Fin N ⊕ Fin N → ℝ =>
            (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
              (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0)) := by
          intro m; induction m with
          | zero =>
              have hEq : (fun v : Fin N ⊕ Fin N → ℝ =>
                  (Finset.range 1).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos 0)⟩
                    (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0)) =
                  fun _ => (0 : ℝ) := by ext v; simp
              rw [hEq]; exact measurable_const
          | succ m ih =>
              have hEq : (fun v : Fin N ⊕ Fin N → ℝ =>
                  (Finset.range (m + 2)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos (m + 1))⟩
                    (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0)) =
                  fun v => max ((Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos m)⟩
                    (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0))
                    (∑ i : Fin N, if i.1 < m + 1 then v (Sum.inr i) - premium * v (Sum.inl i) else 0) := by
                ext v
                exact finset_sup'_range_succ
                  (fun n => ∑ i : Fin N, if i.1 < n then v (Sum.inr i) - premium * v (Sum.inl i) else 0) m
              rw [hEq]; exact ih.max (hterm (m + 1))
        exact haux N
      have hComp' : ∀ m : ℕ, M_fin m N = Ψ ∘ X_tup m := fun m => by
        ext ω
        dsimp only [M_fin, Ψ, Function.comp_apply]
        refine Finset.sup'_congr _ rfl fun n hn => ?_
        have hle : n ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
        have hEq_term : ∀ i : Fin N,
            X_tup m ω (Sum.inr i) - premium * X_tup m ω (Sum.inl i) =
              claims (m + i.1) ω - premium * arrival (m + i.1) ω := fun _ => rfl
        simp_rw [hEq_term]
        dsimp only [S_from, Z]
        rw [← Fin.sum_univ_eq_sum_range (fun i => claims (m + i) ω - premium * arrival (m + i) ω)]
        rw [← Finset.sum_filter]
        refine Finset.sum_nbij (fun j : Fin n => (⟨j.1, lt_of_lt_of_le j.2 hle⟩ : Fin N)) ?_ ?_ ?_ ?_
        · intro j _; simp [j.2]
        · intro j1 _ j2 _ h; exact Fin.ext (by simpa using congrArg Fin.val h)
        · intro i hi
          have hilt : i.1 < n := (Finset.mem_filter.mp hi).2
          exact ⟨⟨i.1, hilt⟩, Finset.mem_univ _, Fin.ext rfl⟩
        · intro j _; rfl
      have hX_meas_fun : ∀ m, Measurable (X_tup m) := fun m => measurable_pi_lambda _ (hX_meas m)
      rw [hComp' k, hComp' 0, ← Measure.map_map hΨ_meas (hX_meas_fun k),
        ← Measure.map_map hΨ_meas (hX_meas_fun 0), hPi_law k, hPi_law 0]
    refine Measure.ext_of_charFun (funext fun ξ => ?_)
    have hTend : ∀ m : ℕ, Tendsto (fun N => charFun (P.map (M_fin m N)) ξ) atTop
        (𝓝 (charFun (P.map (M_from m)) ξ)) := fun m => by
      have hEq : ∀ N, charFun (P.map (M_fin m N)) ξ =
          ∫ ω, Complex.exp ((ξ : ℂ) * (M_fin m N ω : ℂ) * Complex.I) ∂P := fun N => by
        rw [charFun_apply_real]
        exact integral_map (μ := P) (φ := M_fin m N)
          (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
          (hM_fin_meas m N).aemeasurable (by fun_prop)
      have hEqLim : charFun (P.map (M_from m)) ξ =
          ∫ ω, Complex.exp ((ξ : ℂ) * (M_from m ω : ℂ) * Complex.I) ∂P := by
        rw [charFun_apply_real]
        exact integral_map (μ := P) (φ := M_from m)
          (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
          (hM_meas m).aemeasurable (by fun_prop)
      simp_rw [hEq]; rw [hEqLim]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
      · intro N
        exact (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hM_fin_meas m N))).mul
            measurable_const)).aestronglyMeasurable
      · intro N
        refine Filter.Eventually.of_forall fun ω => ?_
        have harg : (ξ : ℂ) * (M_fin m N ω : ℂ) * Complex.I = ((ξ * M_fin m N ω : ℝ) : ℂ) * Complex.I := by
          push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      · filter_upwards [hM_ev_const] with ω hω
        obtain ⟨N0, hConst, _, _⟩ := hω m
        exact tendsto_atTop_of_eventually_const fun N hN => by rw [hConst N hN]
    have hSeq_eq : (fun N => charFun (P.map (M_fin k N)) ξ) =
        fun N => charFun (P.map (M_fin 0 N)) ξ := funext fun N => by rw [hFin_law N]
    have h1 := hTend k
    rw [hSeq_eq] at h1
    exact tendsto_nhds_unique h1 (hTend 0)
  -- Step 5: Tail independence helper for M_from k
  have hM_meas_tail : ∀ k : ℕ,
      @Measurable Ω ℝ (⨆ i ∈ {idx : ℕ ⊕ ℕ | k ≤ Sum.elim id id idx},
        MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance) _ (M_from k) := by
    intro k
    let mTail : MeasurableSpace Ω :=
      ⨆ i ∈ {idx : ℕ ⊕ ℕ | k ≤ Sum.elim id id idx},
        MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance
    have hArr_tail : ∀ i : ℕ, @Measurable Ω ℝ mTail _ (arrival (k + i)) := fun i => by
      have hmem : Sum.inl (k + i) ∈ {idx : ℕ ⊕ ℕ | k ≤ Sum.elim id id idx} := by simp
      have hle : MeasurableSpace.comap (Sum.elim arrival claims (Sum.inl (k + i))) inferInstance ≤ mTail :=
        le_iSup₂_of_le (Sum.inl (k + i)) hmem le_rfl
      exact (comap_measurable (arrival (k + i))).mono hle le_rfl
    have hClm_tail : ∀ i : ℕ, @Measurable Ω ℝ mTail _ (claims (k + i)) := fun i => by
      have hmem : Sum.inr (k + i) ∈ {idx : ℕ ⊕ ℕ | k ≤ Sum.elim id id idx} := by simp
      have hle : MeasurableSpace.comap (Sum.elim arrival claims (Sum.inr (k + i))) inferInstance ≤ mTail :=
        le_iSup₂_of_le (Sum.inr (k + i)) hmem le_rfl
      exact (comap_measurable (claims (k + i))).mono hle le_rfl
    have hS_tail : ∀ n : ℕ, @Measurable Ω ℝ mTail _ (S_from k n) := fun n =>
      measurable_sum_of_space mTail (Finset.range n) (fun i => Z (k + i))
        (fun i _ => (hClm_tail i).sub (measurable_const.mul (hArr_tail i)))
    have hMfin_tail : ∀ N : ℕ, @Measurable Ω ℝ mTail _ (M_fin k N) := fun N => by
      induction N with
      | zero =>
          have hEq : M_fin k 0 = fun _ => (0 : ℝ) := by ext ω; simp [M_fin, S_from]
          rw [hEq]; exact @measurable_const ℝ Ω _ mTail (0 : ℝ)
      | succ N ih =>
          have hEq : M_fin k (N + 1) = fun ω => max (M_fin k N ω) (S_from k (N + 1) ω) := by
            ext ω; exact finset_sup'_range_succ (fun n => S_from k n ω) N
          rw [hEq]; exact ih.max (hS_tail (N + 1))
    exact ENNReal.measurable_toReal.comp
      (measurable_iSup_ennreal_of_space mTail (fun N ω => ENNReal.ofReal (M_fin k N ω))
        fun N => ENNReal.measurable_ofReal.comp (hMfin_tail N))
  have hLe_coord : ∀ idx : ℕ ⊕ ℕ,
      MeasurableSpace.comap (Sum.elim arrival claims idx) inferInstance ≤ ‹MeasurableSpace Ω› := fun idx => by
    cases idx with
    | inl i => exact (hd.measurable_interarrival i).comap_le
    | inr i => exact (hd.measurable_mark i).comap_le
  -- Step 6: Lindley recursion and charFun equation for M_from 0
  have hLindley_ae : ∀ᵐ ω ∂P,
      M_from 0 ω = max 0 (M_from 1 ω + claims 0 ω - premium * arrival 0 ω) := by
    filter_upwards [hM_ev_const] with ω hω
    obtain ⟨N0, _, hle0, ⟨n0, _, heq0⟩⟩ := hω 0
    obtain ⟨N1, _, hle1, ⟨n1, _, heq1⟩⟩ := hω 1
    have hS_succ : ∀ n : ℕ, S_from 0 (n + 1) ω = Z 0 ω + S_from 1 n ω := fun n => by
      dsimp only [S_from]
      rw [Finset.sum_range_succ']
      simp [add_comm]
    apply le_antisymm
    · rw [← heq0]
      rcases n0 with _ | n0
      · simp [S_from]
      · rw [hS_succ n0]
        have h1 : S_from 1 n0 ω ≤ M_from 1 ω := hle1 n0
        have h2 : Z 0 ω + S_from 1 n0 ω ≤ M_from 1 ω + claims 0 ω - premium * arrival 0 ω := by
          dsimp only [Z]; linarith
        exact le_trans h2 (le_max_right _ _)
    · apply max_le (hM_nonneg 0 ω)
      rw [← heq1]
      have h1 : S_from 0 (n1 + 1) ω ≤ M_from 0 ω := hle0 (n1 + 1)
      rw [hS_succ n1] at h1
      dsimp only [Z] at h1
      linarith
  -- Independence of (M_from 1 + claims 0) and (premium * arrival 0), and of M_from 1 and claims 0
  set Z' : Ω → ℝ := fun ω => M_from 1 ω + claims 0 ω
  set E0 : Ω → ℝ := fun ω => premium * arrival 0 ω
  have hZ'_meas : Measurable Z' := (hM_meas 1).add (hd.measurable_mark 0)
  have hE0_meas : Measurable E0 := measurable_const.mul (hd.measurable_interarrival 0)
  have hInd_M1_C0 : IndepFun (M_from 1) (claims 0) P := by
    have hdisj : Disjoint ({idx : ℕ ⊕ ℕ | 1 ≤ Sum.elim id id idx} : Set (ℕ ⊕ ℕ)) {Sum.inr 0} := by
      rw [Set.disjoint_singleton_right]; simp
    have hind := indep_iSup_of_disjoint hLe_coord hd.indep.iIndep hdisj
    have hm1 : MeasurableSpace.comap (M_from 1) inferInstance ≤
        ⨆ i ∈ {idx : ℕ ⊕ ℕ | 1 ≤ Sum.elim id id idx},
          MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance :=
      (hM_meas_tail 1).comap_le
    have hm2 : MeasurableSpace.comap (claims 0) inferInstance ≤
        ⨆ i ∈ ({Sum.inr 0} : Set (ℕ ⊕ ℕ)),
          MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance :=
      le_iSup₂_of_le (Sum.inr 0) (Set.mem_singleton _) le_rfl
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hm1) hm2
  have hInd_Z'_E0 : IndepFun Z' E0 P := by
    have hdisj : Disjoint
        ({idx : ℕ ⊕ ℕ | 1 ≤ Sum.elim id id idx} ∪ {Sum.inr 0} : Set (ℕ ⊕ ℕ)) {Sum.inl 0} := by
      rw [Set.disjoint_singleton_right]; simp
    have hind := indep_iSup_of_disjoint hLe_coord hd.indep.iIndep hdisj
    let mLeft : MeasurableSpace Ω :=
      ⨆ i ∈ ({idx : ℕ ⊕ ℕ | 1 ≤ Sum.elim id id idx} ∪ {Sum.inr 0} : Set (ℕ ⊕ ℕ)),
        MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance
    have hM1_L : @Measurable Ω ℝ mLeft _ (M_from 1) :=
      (hM_meas_tail 1).mono (biSup_mono Set.subset_union_left) le_rfl
    have hC0_L : @Measurable Ω ℝ mLeft _ (claims 0) :=
      (comap_measurable (claims 0)).mono
        (le_iSup₂_of_le (Sum.inr 0) (Set.mem_union_right _ (Set.mem_singleton _)) le_rfl) le_rfl
    have hZ'_L : @Measurable Ω ℝ mLeft _ Z' := hM1_L.add hC0_L
    have hE0_R : @Measurable Ω ℝ
        (⨆ i ∈ ({Sum.inl 0} : Set (ℕ ⊕ ℕ)),
          MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance) _ E0 :=
      (measurable_const.mul (comap_measurable (arrival 0))).mono
        (le_iSup₂_of_le (Sum.inl 0) (Set.mem_singleton _) le_rfl) le_rfl
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hZ'_L.comap_le) hE0_R.comap_le
  have hE0_law : P.map E0 = expMeasure γ := by
    have hcomp : E0 = (fun x => premium * x) ∘ arrival 0 := rfl
    rw [hcomp, ← Measure.map_map (measurable_const_mul premium) (hd.measurable_interarrival 0),
      (hd.law_interarrival 0).map_eq, expMeasure_map_mul_rd hrateR hpremium]
  have hZ'_nonneg_ae : ∀ᵐ ω ∂P, 0 ≤ Z' ω := by
    filter_upwards [hClaimsPos] with ω hCω
    exact add_nonneg (hM_nonneg 1 ω) (hCω 0).le
  have hZ'_charFun : ∀ ξ : ℝ,
      charFun (P.map Z') ξ = charFun (P.map (M_from 0)) ξ * charFun F ξ := fun ξ => by
    let φ : ℝ → ℂ := fun x => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)
    have hφ_meas : Measurable φ :=
      Complex.continuous_exp.measurable.comp
        ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const)
    have hInd_exp : IndepFun (φ ∘ M_from 1) (φ ∘ claims 0) P :=
      hInd_M1_C0.comp hφ_meas hφ_meas
    have h1 := hInd_exp.integral_fun_mul_eq_mul_integral
      (hφ_meas.comp (hM_meas 1)).aestronglyMeasurable
      (hφ_meas.comp (hd.measurable_mark 0)).aestronglyMeasurable
    have hL : charFun (P.map Z') ξ =
        ∫ ω, (φ ∘ M_from 1) ω * (φ ∘ claims 0) ω ∂P := by
      rw [charFun_apply_real, integral_map (μ := P) (φ := Z') (f := φ)
        hZ'_meas.aemeasurable hφ_meas.aestronglyMeasurable]
      congr 1; ext ω; dsimp only [Z', φ, Function.comp_apply]; rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hR1 : (∫ ω, (φ ∘ M_from 1) ω ∂P) = charFun (P.map (M_from 0)) ξ := by
      rw [← hM_law_eq 1, charFun_apply_real, integral_map (μ := P) (φ := M_from 1) (f := φ)
        (hM_meas 1).aemeasurable hφ_meas.aestronglyMeasurable]
      rfl
    have hR2 : (∫ ω, (φ ∘ claims 0) ω ∂P) = charFun F ξ := by
      rw [← (hd.law_mark 0).map_eq, charFun_apply_real, integral_map (μ := P) (φ := claims 0) (f := φ)
        (hd.measurable_mark 0).aemeasurable hφ_meas.aestronglyMeasurable]
      rfl
    rw [hL, h1, hR1, hR2]
  -- Define p0 = ∫ exp(-γ Z') dP and show p0 = (P {M_from 0 = 0}).toReal
  set p0 : ℝ := ∫ ω, Real.exp (-γ * Z' ω) ∂P
  have hp0_eq : p0 = (P {ω | M_from 0 ω = 0}).toReal := by
    have hmap_prod : P.map (fun ω => (Z' ω, E0 ω)) = (P.map Z').prod (expMeasure γ) := by
      rw [← hE0_law]
      exact (indepFun_iff_map_prod_eq_prod_map_map hZ'_meas.aemeasurable hE0_meas.aemeasurable).mp hInd_Z'_E0
    have hEq_set : {ω | M_from 0 ω = 0} =ᵐ[P] {ω | Z' ω ≤ E0 ω} := by
      filter_upwards [hLindley_ae] with ω hL
      change (M_from 0 ω = 0) = (Z' ω ≤ E0 ω)
      rw [hL]
      apply propext
      dsimp only [Z', E0]
      constructor
      · intro h; have : M_from 1 ω + claims 0 ω - premium * arrival 0 ω ≤ 0 := by
          have := le_max_right (0 : ℝ) (M_from 1 ω + claims 0 ω - premium * arrival 0 ω)
          linarith
        linarith
      · intro h; exact max_eq_left (by linarith)
    have hMeasS : MeasurableSet {p : ℝ × ℝ | p.1 ≤ p.2} :=
      measurableSet_le measurable_fst measurable_snd
    have hP_eq : P {ω | Z' ω ≤ E0 ω} = ((P.map Z').prod (expMeasure γ)) {p : ℝ × ℝ | p.1 ≤ p.2} := by
      rw [← hmap_prod, Measure.map_apply (hZ'_meas.prodMk hE0_meas) hMeasS]; rfl
    have : IsProbabilityMeasure (expMeasure γ) := isProbabilityMeasure_expMeasure hγ
    have : IsProbabilityMeasure (P.map Z') := Measure.isProbabilityMeasure_map hZ'_meas.aemeasurable
    rw [measure_congr hEq_set, hP_eq, Measure.prod_apply hMeasS]
    have hZ'_nn_map : ∀ᵐ z ∂(P.map Z'), 0 ≤ z :=
      (ae_map_iff hZ'_meas.aemeasurable (measurableSet_le measurable_const measurable_id)).mpr hZ'_nonneg_ae
    have hInner_l : ∀ᵐ z ∂(P.map Z'),
        expMeasure γ (Prod.mk z ⁻¹' {p : ℝ × ℝ | p.1 ≤ p.2}) = ENNReal.ofReal (Real.exp (-γ * z)) := by
      filter_upwards [hZ'_nn_map] with z hz
      have hpre : Prod.mk z ⁻¹' {p : ℝ × ℝ | p.1 ≤ p.2} = Set.Ici z := rfl
      rw [hpre]
      have hIci_eq : expMeasure γ (Set.Ici z) = expMeasure γ (Set.Ioi z) := by
        have hdiff : Set.Ici z = Set.Ioi z ∪ {z} := by ext t; simp [le_iff_lt_or_eq, or_comm]
        rw [hdiff, measure_union (Set.disjoint_singleton_right.mpr Set.self_notMem_Ioi)
          (measurableSet_singleton z)]
        have hsing : expMeasure γ {z} = 0 := by
          rw [expMeasure, gammaMeasure, withDensity_apply _ (measurableSet_singleton z),
            Measure.restrict_singleton, measure_singleton]
          simp
        rw [hsing, add_zero]
      rw [hIci_eq]
      have hcompl : expMeasure γ (Set.Ioi z) = 1 - expMeasure γ (Set.Iic z) := by
        rw [← Set.compl_Iic, prob_compl_eq_one_sub measurableSet_Iic]
      rw [hcompl]
      have hcdf : (expMeasure γ (Set.Iic z)).toReal = 1 - Real.exp (-(γ * z)) := by
        have h1 : (expMeasure γ (Set.Iic z)).toReal = cdf (expMeasure γ) z := by
          rw [cdf_eq_real, Measure.real]
        rw [h1, cdf_expMeasure_eq hγ, if_pos hz]
      have hle1 : expMeasure γ (Set.Iic z) ≤ 1 := prob_le_one
      have htoR : (1 - expMeasure γ (Set.Iic z)).toReal = Real.exp (-γ * z) := by
        rw [ENNReal.toReal_sub_of_le hle1 ENNReal.one_ne_top, ENNReal.toReal_one, hcdf]
        ring_nf
      rw [← htoR, ENNReal.ofReal_toReal (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self)]
    rw [lintegral_congr_ae hInner_l]
    have hInt_exp : Integrable (fun z : ℝ => Real.exp (-γ * z)) (P.map Z') := by
      refine (integrable_const (1 : ℝ)).mono'
        (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).aestronglyMeasurable ?_
      filter_upwards [hZ'_nn_map] with z hz
      rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact Real.exp_le_one_iff.mpr (by nlinarith)
    rw [← ofReal_integral_eq_lintegral_ofReal hInt_exp
      (Filter.Eventually.of_forall fun z => (Real.exp_pos _).le),
      ENNReal.toReal_ofReal (integral_nonneg fun z => (Real.exp_pos _).le)]
    exact (integral_map (μ := P) (φ := Z') (f := fun z : ℝ => Real.exp (-γ * z))
      hZ'_meas.aemeasurable (by fun_prop)).symm
  -- Core Lindley charFun equation: ((γ : ℂ) + I * ξ) * φ_M(ξ) = γ * φ_M(ξ) * φ_F(ξ) + I * ξ * p0
  have hLindley_cf : ∀ ξ : ℝ,
      ((γ : ℂ) + Complex.I * (ξ : ℂ)) * charFun (P.map (M_from 0)) ξ =
        (γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ +
          Complex.I * (ξ : ℂ) * (p0 : ℂ) := by
    intro ξ
    have hden_ne : ((γ : ℂ) + Complex.I * (ξ : ℂ)) ≠ 0 := by
      intro h0; have hre := congrArg Complex.re h0; simp at hre; linarith
    have : IsProbabilityMeasure (expMeasure γ) := isProbabilityMeasure_expMeasure hγ
    have : IsProbabilityMeasure (P.map Z') := Measure.isProbabilityMeasure_map hZ'_meas.aemeasurable
    have hmap_prod : P.map (fun ω => (Z' ω, E0 ω)) = (P.map Z').prod (expMeasure γ) := by
      rw [← hE0_law]
      exact (indepFun_iff_map_prod_eq_prod_map_map hZ'_meas.aemeasurable hE0_meas.aemeasurable).mp hInd_Z'_E0
    let H : ℝ × ℝ → ℂ := fun p =>
      Complex.exp (((ξ : ℂ) * ((max 0 (p.1 - p.2) : ℝ) : ℂ)) * Complex.I)
    have hH_meas : Measurable H :=
      Complex.continuous_exp.measurable.comp
        ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (measurable_const.max (measurable_fst.sub measurable_snd)))).mul measurable_const)
    have hH_int : Integrable H ((P.map Z').prod (expMeasure γ)) := by
      refine (integrable_const (1 : ℝ)).mono' hH_meas.aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun p => ?_
      dsimp only [H]
      have harg : ((ξ : ℂ) * ((max 0 (p.1 - p.2) : ℝ) : ℂ)) * Complex.I =
          ((ξ * max 0 (p.1 - p.2) : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    have hcf_M : charFun (P.map (M_from 0)) ξ =
        ∫ z, (∫ t, H (z, t) ∂(expMeasure γ)) ∂(P.map Z') := by
      rw [charFun_apply_real, integral_map (μ := P) (φ := M_from 0)
        (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
        (hM_meas 0).aemeasurable (by fun_prop)]
      have hcongr : (∫ ω, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) =
          ∫ ω, H (Z' ω, E0 ω) ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hLindley_ae] with ω hL
        rw [hL]
      rw [hcongr, ← integral_map (hZ'_meas.prodMk hE0_meas).aemeasurable hH_meas.aestronglyMeasurable,
        hmap_prod, integral_prod H hH_int]
    have hZ'_nn_map : ∀ᵐ z ∂(P.map Z'), 0 ≤ z :=
      (ae_map_iff hZ'_meas.aemeasurable (measurableSet_le measurable_const measurable_id)).mpr hZ'_nonneg_ae
    have hInner_eval : ∀ᵐ z ∂(P.map Z'),
        (∫ t, H (z, t) ∂(expMeasure γ)) =
          ((γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) +
            Complex.I * (ξ : ℂ) * ((Real.exp (-γ * z) : ℝ) : ℂ)) /
            ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
      filter_upwards [hZ'_nn_map] with z hz
      exact expMeasure_lindley_charFun hγ hz
    have hInt1 : Integrable (fun z : ℝ => (γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I))
        (P.map Z') := by
      refine ((integrable_const (γ : ℝ)).mono'
        (measurable_const.mul (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const))).aestronglyMeasurable ?_)
      refine Filter.Eventually.of_forall fun z => ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hγ]
      have harg : (ξ : ℂ) * (z : ℂ) * Complex.I = ((ξ * z : ℝ) : ℂ) * Complex.I := by push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I, mul_one]
    have hInt2 : Integrable (fun z : ℝ => Complex.I * (ξ : ℂ) * ((Real.exp (-γ * z) : ℝ) : ℂ))
        (P.map Z') := by
      refine ((integrable_const |ξ|).mono'
        (measurable_const.mul (Complex.continuous_ofReal.measurable.comp
          (Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)))).aestronglyMeasurable ?_)
      filter_upwards [hZ'_nn_map] with z hz
      rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      have hle1 : Real.exp (-γ * z) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
      nlinarith [abs_nonneg ξ]
    have hof2 : (∫ z, ((Real.exp (-γ * z) : ℝ) : ℂ) ∂(P.map Z')) = (p0 : ℂ) := by
      have hof : (∫ z, ((Real.exp (-γ * z) : ℝ) : ℂ) ∂(P.map Z')) =
          ((∫ z, Real.exp (-γ * z) ∂(P.map Z') : ℝ) : ℂ) := integral_ofReal
      rw [hof, integral_map (μ := P) (φ := Z') (f := fun z : ℝ => Real.exp (-γ * z))
        hZ'_meas.aemeasurable (by fun_prop)]
    have hEq_div : charFun (P.map (M_from 0)) ξ =
        ((γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ +
          Complex.I * (ξ : ℂ) * (p0 : ℂ)) / ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
      calc charFun (P.map (M_from 0)) ξ
          = ∫ z, (∫ t, H (z, t) ∂(expMeasure γ)) ∂(P.map Z') := hcf_M
        _ = ∫ z, ((γ : ℂ) * Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I) +
              Complex.I * (ξ : ℂ) * ((Real.exp (-γ * z) : ℝ) : ℂ)) /
              ((γ : ℂ) + Complex.I * (ξ : ℂ)) ∂(P.map Z') := integral_congr_ae hInner_eval
        _ = ((γ : ℂ) * charFun (P.map Z') ξ + Complex.I * (ξ : ℂ) * (p0 : ℂ)) /
              ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
            rw [integral_div, integral_add hInt1 hInt2, integral_const_mul, integral_const_mul,
              ← charFun_apply_real, hof2]
        _ = ((γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ +
              Complex.I * (ξ : ℂ) * (p0 : ℂ)) / ((γ : ℂ) + Complex.I * (ξ : ℂ)) := by
            rw [hZ'_charFun ξ]; ring
    calc ((γ : ℂ) + Complex.I * (ξ : ℂ)) * charFun (P.map (M_from 0)) ξ
        = ((γ : ℂ) + Complex.I * (ξ : ℂ)) *
            (((γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ +
              Complex.I * (ξ : ℂ) * (p0 : ℂ)) / ((γ : ℂ) + Complex.I * (ξ : ℂ))) := by
            rw [← hEq_div]
      _ = (γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ +
            Complex.I * (ξ : ℂ) * (p0 : ℂ) := mul_div_cancel₀ _ hden_ne
  -- Deduce φ_M(ξ) * (1 - ρ * charFun eta ξ) = p0 for all ξ ≠ 0, then p0 = 1 - ρ
  have hFactor_nz : ∀ ξ : ℝ, ξ ≠ 0 →
      charFun (P.map (M_from 0)) ξ * (1 - (ρ : ℂ) * charFun eta ξ) = (p0 : ℂ) := by
    intro ξ hξ
    have hcf := hLindley_cf ξ
    have heta_cf := integratedTail_charFun F mu hmu hclaimpos hclaimint hmean eta hetaSupp hetaCDF ξ hξ
    have hξ_ne : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
    have hmu_ne : (mu : ℂ) ≠ 0 := by exact_mod_cast hmu.ne'
    have hprem_ne : (premium : ℂ) ≠ 0 := by exact_mod_cast hpremium.ne'
    have hρ_eq : (ρ : ℂ) = (γ : ℂ) * (mu : ℂ) := by
      dsimp only [ρ, γ]; push_cast; field_simp [hprem_ne]
    rw [heta_cf, hρ_eq]
    have h1 : Complex.I * (ξ : ℂ) * (charFun (P.map (M_from 0)) ξ *
        (1 - (γ : ℂ) * (mu : ℂ) * ((charFun F ξ - 1) / ((ξ : ℂ) * Complex.I * (mu : ℂ))))) =
        Complex.I * (ξ : ℂ) * (p0 : ℂ) := by
      have hsimp : Complex.I * (ξ : ℂ) * (1 - (γ : ℂ) * (mu : ℂ) *
          ((charFun F ξ - 1) / ((ξ : ℂ) * Complex.I * (mu : ℂ)))) =
          Complex.I * (ξ : ℂ) - (γ : ℂ) * (charFun F ξ - 1) := by
        field_simp [hξ_ne, Complex.I_ne_zero, hmu_ne]
      calc Complex.I * (ξ : ℂ) * (charFun (P.map (M_from 0)) ξ *
              (1 - (γ : ℂ) * (mu : ℂ) * ((charFun F ξ - 1) / ((ξ : ℂ) * Complex.I * (mu : ℂ)))))
          = charFun (P.map (M_from 0)) ξ * (Complex.I * (ξ : ℂ) *
              (1 - (γ : ℂ) * (mu : ℂ) * ((charFun F ξ - 1) / ((ξ : ℂ) * Complex.I * (mu : ℂ))))) := by ring
        _ = charFun (P.map (M_from 0)) ξ * (Complex.I * (ξ : ℂ) - (γ : ℂ) * (charFun F ξ - 1)) := by
              rw [hsimp]
        _ = ((γ : ℂ) + Complex.I * (ξ : ℂ)) * charFun (P.map (M_from 0)) ξ -
              (γ : ℂ) * charFun (P.map (M_from 0)) ξ * charFun F ξ := by ring
        _ = Complex.I * (ξ : ℂ) * (p0 : ℂ) := by rw [hcf]; ring
    exact mul_left_cancel₀ (mul_ne_zero Complex.I_ne_zero hξ_ne) h1
  -- Continuity of charFun at 0 yields p0 = 1 - ρ
  have hp0_val : p0 = 1 - ρ := by
    have hCont_cf : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν],
        Tendsto (fun n : ℕ => charFun ν (1 / ((n : ℝ) + 1))) atTop (𝓝 (1 : ℂ)) := by
      intro ν _
      have hEq : ∀ n : ℕ, charFun ν (1 / ((n : ℝ) + 1)) =
          ∫ x, Complex.exp (((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (x : ℂ) * Complex.I) ∂ν := fun n =>
        charFun_apply_real _
      simp_rw [hEq]
      have hLim : (1 : ℂ) = ∫ _x : ℝ, (1 : ℂ) ∂ν := by simp
      rw [hLim]
      refine tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ)) ?_ (integrable_const 1) ?_ ?_
      · intro n
        exact (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul Complex.continuous_ofReal.measurable).mul measurable_const)).aestronglyMeasurable
      · intro n
        refine Filter.Eventually.of_forall fun x => ?_
        have harg : ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (x : ℂ) * Complex.I =
            (((1 / ((n : ℝ) + 1)) * x : ℝ) : ℂ) * Complex.I := by push_cast; ring
        rw [harg, Complex.norm_exp_ofReal_mul_I]
      · refine Filter.Eventually.of_forall fun x => ?_
        have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
          tendsto_one_div_add_atTop_nhds_zero_nat
        have hmul : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ) * (x : ℂ) * Complex.I)
            atTop (𝓝 (((0 : ℝ) : ℂ) * (x : ℂ) * Complex.I)) :=
          ((Complex.continuous_ofReal.continuousAt.tendsto.comp hinv).mul tendsto_const_nhds).mul
            tendsto_const_nhds
        simpa [Function.comp_def] using Complex.continuous_exp.continuousAt.tendsto.comp hmul
    have : IsProbabilityMeasure (P.map (M_from 0)) := Measure.isProbabilityMeasure_map (hM_meas 0).aemeasurable
    have h1 := hCont_cf (P.map (M_from 0))
    have h2 := hCont_cf eta
    have hProd : Tendsto (fun n : ℕ =>
        charFun (P.map (M_from 0)) (1 / ((n : ℝ) + 1)) *
          (1 - (ρ : ℂ) * charFun eta (1 / ((n : ℝ) + 1)))) atTop (𝓝 (1 * (1 - (ρ : ℂ) * 1))) :=
      h1.mul (tendsto_const_nhds.sub (tendsto_const_nhds.mul h2))
    have hConst : (fun n : ℕ =>
        charFun (P.map (M_from 0)) (1 / ((n : ℝ) + 1)) *
          (1 - (ρ : ℂ) * charFun eta (1 / ((n : ℝ) + 1)))) = fun _ => (p0 : ℂ) := by
      ext n
      exact hFactor_nz _ (by positivity)
    rw [hConst] at hProd
    have hC : (p0 : ℂ) = ((1 - ρ : ℝ) : ℂ) := by
      have h := tendsto_nhds_unique tendsto_const_nhds hProd
      simpa using h
    exact_mod_cast hC
  have hFactor_all : ∀ ξ : ℝ,
      charFun (P.map (M_from 0)) ξ * (1 - (ρ : ℂ) * charFun eta ξ) = ((1 - ρ : ℝ) : ℂ) := by
    intro ξ
    by_cases hξ : ξ = 0
    · subst hξ
      have : IsProbabilityMeasure (P.map (M_from 0)) := Measure.isProbabilityMeasure_map (hM_meas 0).aemeasurable
      simp [charFun_zero]
    · rw [← hp0_val]; exact hFactor_nz ξ hξ
  -- Step 7: Relate ruinEvent 0 and ruinDeficit 0 to M_from 0 and first ascending ladder epoch E k
  let E : ℕ → Set Ω := fun k =>
    {ω | (∀ j < k, S_from 0 (j + 1) ω ≤ 0) ∧ 0 < S_from 0 (k + 1) ω}
  have hE_meas : ∀ k, MeasurableSet (E k) := fun k => by
    have h1 : MeasurableSet {ω | ∀ j < k, S_from 0 (j + 1) ω ≤ 0} := by
      have hEq : {ω | ∀ j < k, S_from 0 (j + 1) ω ≤ 0} =
          ⋂ j ∈ Finset.range k, {ω | S_from 0 (j + 1) ω ≤ 0} := by ext ω; simp
      rw [hEq]
      exact MeasurableSet.biInter (Finset.countable_toSet _) fun j _ =>
        measurableSet_le (hS_meas 0 (j + 1)) measurable_const
    exact h1.inter (measurableSet_lt measurable_const (hS_meas 0 (k + 1)))
  have hE_disj : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    Set.disjoint_left.mpr fun ω hi hj => by
      rcases lt_or_gt_of_ne hij with hlt | hgt
      · linarith [hj.1 i hlt, hi.2]
      · linarith [hi.1 j hgt, hj.2]
  have hGood_ruin : ∀ᵐ ω ∂P,
      (ω ∈ ruinEvent arrival claims premium 0 ↔ ∃ k : ℕ, ω ∈ E k) ∧
      (ω ∈ ruinEvent arrival claims premium 0 ↔ 0 < M_from 0 ω) ∧
      (∀ k : ℕ, ω ∈ E k →
        ruinDeficit arrival claims premium 0 ω = S_from 0 (k + 1) ω ∧
        M_from 0 ω = S_from 0 (k + 1) ω + M_from (k + 1) ω) := by
    filter_upwards [hArrPos, hStrict, hTendsto, hClaimsPos, hM_ev_const] with
      ω hPosω hStrictω hTendstoω hClmω hMω
    have hSurp_arr : ∀ k : ℕ,
        riskSurplus arrival claims premium 0
          ⟨ProbabilityTheory.arrival arrival k ω, (by
            have h0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
              simpa [ProbabilityTheory.arrival] using hPosω 0
            exact le_trans h0.le (hStrictω.monotone (Nat.zero_le k)))⟩ ω =
        -S_from 0 (k + 1) ω := fun k => by
      have hJC : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
          (ProbabilityTheory.arrival arrival k ω) = k + 1 := by
        apply le_antisymm
        · by_contra hgt
          have hlt : k + 1 < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
              (ProbabilityTheory.arrival arrival k ω) := lt_of_not_ge hgt
          have hle := (lt_jumpCount_iff hStrictω hTendstoω (k + 1) _).mp hlt
          exact not_lt_of_ge hle (hStrictω (Nat.lt_succ_self k))
        · have hlt : k < jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
              (ProbabilityTheory.arrival arrival k ω) :=
            (lt_jumpCount_iff hStrictω hTendstoω k _).mpr le_rfl
          omega
      unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson ProbabilityTheory.piecewisePath
      change 0 + premium * ProbabilityTheory.arrival arrival k ω -
        (0 + 0 * ProbabilityTheory.arrival arrival k ω +
          ∑ x ∈ Finset.range (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω)
            (ProbabilityTheory.arrival arrival k ω)), claims x ω) = -S_from 0 (k + 1) ω
      rw [hJC]
      simp only [S_from, Z, zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum, ProbabilityTheory.arrival]
      ring
    have hSurp_ge : ∀ t : ℝ≥0, 0 < t →
        (jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) = 0 →
          0 < riskSurplus arrival claims premium 0 t ω) ∧
        (∀ j : ℕ, jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) = j + 1 →
          -S_from 0 (j + 1) ω ≤ riskSurplus arrival claims premium 0 t ω) := fun t ht => by
      constructor
      · intro hj0
        unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson ProbabilityTheory.piecewisePath
        rw [hj0]
        simp only [Finset.range_zero, Finset.sum_empty]
        have htR : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht
        nlinarith
      · intro j hjj
        have hTj_le : ProbabilityTheory.arrival arrival j ω ≤ (t : ℝ) :=
          (lt_jumpCount_iff hStrictω hTendstoω j (t : ℝ)).mp (by omega)
        unfold riskSurplus aggregateClaims ProbabilityTheory.compoundPoisson ProbabilityTheory.piecewisePath
        rw [hjj]
        simp only [S_from, Z, zero_add, Finset.sum_sub_distrib, ← Finset.mul_sum]
        unfold ProbabilityTheory.arrival at hTj_le
        nlinarith
    have hRuin_iff_ex : ω ∈ ruinEvent arrival claims premium 0 ↔ ∃ n : ℕ, 0 < S_from 0 (n + 1) ω := by
      constructor
      · rintro ⟨t, ht, hneg⟩
        rcases hj : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) with _ | j
        · linarith [(hSurp_ge t ht).1 hj]
        · exact ⟨j, by linarith [(hSurp_ge t ht).2 j hj]⟩
      · rintro ⟨n, hpos⟩
        have hTn_pos : 0 < ProbabilityTheory.arrival arrival n ω := by
          have h0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
            simpa [ProbabilityTheory.arrival] using hPosω 0
          exact lt_of_lt_of_le h0 (hStrictω.monotone (Nat.zero_le n))
        refine ⟨⟨ProbabilityTheory.arrival arrival n ω, hTn_pos.le⟩, NNReal.coe_pos.mp hTn_pos, ?_⟩
        rw [hSurp_arr n]; linarith
    have hEx_iff_E : (∃ n : ℕ, 0 < S_from 0 (n + 1) ω) ↔ ∃ k : ℕ, ω ∈ E k := by
      classical
      constructor
      · intro hex
        refine ⟨Nat.find hex, fun j hj => not_lt.mp (Nat.find_min hex hj), Nat.find_spec hex⟩
      · rintro ⟨k, _, hk⟩; exact ⟨k, hk⟩
    have hEx_iff_M : (∃ n : ℕ, 0 < S_from 0 (n + 1) ω) ↔ 0 < M_from 0 ω := by
      obtain ⟨_, _, hle0, ⟨n0, _, heq0⟩⟩ := hMω 0
      constructor
      · rintro ⟨n, hpos⟩; exact lt_of_lt_of_le hpos (hle0 (n + 1))
      · intro hpos
        rw [← heq0] at hpos
        rcases n0 with _ | n0
        · simp [S_from] at hpos
        · exact ⟨n0, hpos⟩
    refine ⟨hRuin_iff_ex.trans hEx_iff_E, hRuin_iff_ex.trans hEx_iff_M, fun k hk => ?_⟩
    have hTk_pos : 0 < ProbabilityTheory.arrival arrival k ω := by
      have h0 : 0 < ProbabilityTheory.arrival arrival 0 ω := by
        simpa [ProbabilityTheory.arrival] using hPosω 0
      exact lt_of_lt_of_le h0 (hStrictω.monotone (Nat.zero_le k))
    set tk : ℝ≥0 := ⟨ProbabilityTheory.arrival arrival k ω, hTk_pos.le⟩
    have hRT_eq : ruinTime arrival claims premium 0 ω = tk := by
      dsimp only [ruinTime]
      apply le_antisymm
      · refine csInf_le ⟨0, fun _ _ => zero_le⟩ ?_
        exact ⟨NNReal.coe_pos.mp hTk_pos, by rw [hSurp_arr k]; linarith [hk.2]⟩
      · refine le_csInf ⟨tk, NNReal.coe_pos.mp hTk_pos, by rw [hSurp_arr k]; linarith [hk.2]⟩ ?_
        rintro t ⟨ht, hneg⟩
        by_contra hlt
        have ht_lt : (t : ℝ) < ProbabilityTheory.arrival arrival k ω := NNReal.coe_lt_coe.mpr (lt_of_not_ge hlt)
        rcases hj : jumpCount (fun n => ProbabilityTheory.arrival arrival n ω) (t : ℝ) with _ | j
        · linarith [(hSurp_ge t ht).1 hj]
        · have hjlt : j < k := by
            by_contra hge
            have hkj : k ≤ j := le_of_not_gt hge
            have hTj_le : ProbabilityTheory.arrival arrival j ω ≤ (t : ℝ) :=
              (lt_jumpCount_iff hStrictω hTendstoω j (t : ℝ)).mp (by omega)
            have hTk_le := le_trans (hStrictω.monotone hkj) hTj_le
            linarith
          linarith [(hSurp_ge t ht).2 j hj, hk.1 j hjlt]
    have hDef_eq : ruinDeficit arrival claims premium 0 ω = S_from 0 (k + 1) ω := by
      dsimp only [ruinDeficit]
      rw [hRT_eq, hSurp_arr k, neg_neg]
    have hM_split : M_from 0 ω = S_from 0 (k + 1) ω + M_from (k + 1) ω := by
      obtain ⟨_, _, hle0, ⟨n0, _, heq0⟩⟩ := hMω 0
      obtain ⟨_, _, hlek, ⟨nk, _, heqk⟩⟩ := hMω (k + 1)
      have hS_add : ∀ n : ℕ, S_from 0 (k + 1 + n) ω = S_from 0 (k + 1) ω + S_from (k + 1) n ω := fun n => by
        dsimp only [S_from]; simp only [zero_add]; exact Finset.sum_range_add (fun i => Z i ω) (k + 1) n
      apply le_antisymm
      · rw [← heq0]
        by_cases hle : n0 ≤ k
        · have hS0_le : S_from 0 n0 ω ≤ 0 := by
            rcases n0 with _ | n0
            · simp [S_from]
            · exact hk.1 n0 (by omega)
          linarith [hk.2, hM_nonneg (k + 1) ω]
        · have hge : k + 1 ≤ n0 := by omega
          have hsub : n0 = k + 1 + (n0 - (k + 1)) := by omega
          rw [hsub, hS_add]
          linarith [hlek (n0 - (k + 1))]
      · rw [← heqk, ← hS_add nk]
        exact hle0 (k + 1 + nk)
    exact ⟨hDef_eq, hM_split⟩
  -- Part 1 of theorem: ruinProbability 0 = ρ
  have hRuin0_prob : ruinProbability P arrival claims premium 0 = ρ := by
    dsimp only [ruinProbability]
    have hEq : ruinEvent arrival claims premium 0 =ᵐ[P] {ω | 0 < M_from 0 ω} := by
      filter_upwards [hGood_ruin] with ω hω
      exact propext hω.2.1
    have hCompl : {ω | 0 < M_from 0 ω} = {ω | M_from 0 ω = 0}ᶜ := by
      ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff]
      exact ⟨ne_of_gt, fun h => lt_of_le_of_ne (hM_nonneg 0 ω) (Ne.symm h)⟩
    rw [measure_congr hEq, hCompl, prob_compl_eq_one_sub (measurableSet_eq_fun (hM_meas 0) measurable_const),
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one,
      ← hp0_eq, hp0_val]
    ring
  -- Step 8: Ladder-height charFun decomposition → (P.restrict (ruinEvent 0)).map (ruinDeficit 0) = ρ • eta
  -- Define measurable version H1 agreeing a.e. with ruinDeficit 0 on ruinEvent 0
  let H1 : Ω → ℝ := fun ω =>
    ∑' k : ℕ, (E k).indicator (S_from 0 (k + 1)) ω
  have hH1_eq : ∀ᵐ ω ∂P, ∀ k : ℕ, ω ∈ E k → H1 ω = S_from 0 (k + 1) ω := by
    refine Filter.Eventually.of_forall fun ω k hk => ?_
    dsimp only [H1]
    rw [tsum_eq_single k]
    · exact Set.indicator_of_mem hk _
    · intro j hjk
      have hnot : ω ∉ E j := Set.disjoint_left.mp (hE_disj hjk.symm) hk
      exact Set.indicator_of_notMem hnot _
  have hH1_meas : Measurable H1 := by
    have hLim : ∀ ω : Ω, Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, (E k).indicator (S_from 0 (k + 1)) ω)
        atTop (𝓝 (H1 ω)) := fun ω => by
      by_cases hex : ∃ k, ω ∈ E k
      · obtain ⟨k, hk⟩ := hex
        have hEq_k : H1 ω = S_from 0 (k + 1) ω := by
          dsimp only [H1]
          rw [tsum_eq_single k]
          · exact Set.indicator_of_mem hk _
          · intro j hjk
            exact Set.indicator_of_notMem (Set.disjoint_left.mp (hE_disj hjk.symm) hk) _
        rw [hEq_k]
        refine tendsto_atTop_of_eventually_const (i₀ := k + 1) fun N hN => ?_
        rw [Finset.sum_eq_single k]
        · exact Set.indicator_of_mem hk _
        · intro j _ hjk
          exact Set.indicator_of_notMem (Set.disjoint_left.mp (hE_disj hjk.symm) hk) _
        · intro hkN; exact absurd (Finset.mem_range.mpr (by omega)) hkN
      · push Not at hex
        have h0 : H1 ω = 0 := by
          dsimp only [H1]
          simp [Set.indicator_of_notMem (hex _)]
        rw [h0]
        refine tendsto_atTop_of_eventually_const (i₀ := 0) fun N _ => ?_
        simp [Set.indicator_of_notMem (hex _)]
    exact measurable_of_tendsto_metrizable
      (fun N => Finset.measurable_sum (Finset.range N) fun k _ => (hS_meas 0 (k + 1)).indicator (hE_meas k))
      (tendsto_pi_nhds.mpr hLim)
  set U : Set Ω := ⋃ k : ℕ, E k
  have hU_meas : MeasurableSet U := MeasurableSet.iUnion hE_meas
  have hRuin_eq_U : ruinEvent arrival claims premium 0 =ᵐ[P] U := by
    filter_upwards [hGood_ruin] with ω hω
    change (ω ∈ ruinEvent arrival claims premium 0) = (ω ∈ U)
    dsimp only [U]
    rw [Set.mem_iUnion]
    exact propext hω.1
  have hDef_eq_H1_on_U : ∀ᵐ ω ∂(P.restrict U), ruinDeficit arrival claims premium 0 ω = H1 ω := by
    rw [ae_restrict_iff' hU_meas]
    filter_upwards [hGood_ruin, hH1_eq] with ω hω hH1ω hmemU
    obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hmemU
    rw [(hω.2.2 k hk).1, hH1ω k hk]
  -- Independence of (1_{E k} * exp(i ξ S_{k+1})) and M_from (k+1)
  have hLadder_cf : ∀ ξ : ℝ,
      charFun ((P.restrict U).map H1) ξ = charFun (ENNReal.ofReal ρ • eta) ξ := by
    intro ξ
    have hM_term : ∀ k : ℕ,
        (∫ ω in E k, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) =
          (∫ ω in E k, Complex.exp ((ξ : ℂ) * (S_from 0 (k + 1) ω : ℂ) * Complex.I) ∂P) *
            charFun (P.map (M_from 0)) ξ := by
      intro k
      let f1 : Ω → ℂ := (E k).indicator (fun ω => Complex.exp ((ξ : ℂ) * (S_from 0 (k + 1) ω : ℂ) * Complex.I))
      let f2 : Ω → ℂ := fun ω => Complex.exp ((ξ : ℂ) * (M_from (k + 1) ω : ℂ) * Complex.I)
      have hf1_meas : Measurable f1 :=
        (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hS_meas 0 (k + 1)))).mul
            measurable_const)).indicator (hE_meas k)
      have hf2_meas : Measurable f2 :=
        Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hM_meas (k + 1)))).mul
            measurable_const)
      have hInd_k : IndepFun f1 f2 P := by
        have hdisj : Disjoint ({idx : ℕ ⊕ ℕ | Sum.elim id id idx < k + 1} : Set (ℕ ⊕ ℕ))
            {idx : ℕ ⊕ ℕ | k + 1 ≤ Sum.elim id id idx} :=
          Set.disjoint_left.mpr fun idx h1 h2 =>
            not_lt_of_ge (show k + 1 ≤ Sum.elim id id idx from h2) (show Sum.elim id id idx < k + 1 from h1)
        have hind := indep_iSup_of_disjoint hLe_coord hd.indep.iIndep hdisj
        let mPast : MeasurableSpace Ω :=
          ⨆ i ∈ {idx : ℕ ⊕ ℕ | Sum.elim id id idx < k + 1},
            MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance
        have hS_past : ∀ m ≤ k + 1, @Measurable Ω ℝ mPast _ (S_from 0 m) := fun m hm =>
          measurable_sum_of_space mPast (Finset.range m) (fun i => Z (0 + i)) fun i hi => by
            have hilt : i < k + 1 := lt_of_lt_of_le (Finset.mem_range.mp hi) hm
            have hA : @Measurable Ω ℝ mPast _ (arrival i) :=
              (comap_measurable (arrival i)).mono
                (le_iSup₂_of_le (Sum.inl i) (by simpa using hilt) le_rfl) le_rfl
            have hC : @Measurable Ω ℝ mPast _ (claims i) :=
              (comap_measurable (claims i)).mono
                (le_iSup₂_of_le (Sum.inr i) (by simpa using hilt) le_rfl) le_rfl
            simpa only [Z, zero_add] using measurable_sub_const_mul_of_space mPast premium (claims i) (arrival i) hC hA
        have hEk_past : MeasurableSet[mPast] (E k) := by
          have h1 : MeasurableSet[mPast] {ω | ∀ j < k, S_from 0 (j + 1) ω ≤ 0} := by
            have hEq : {ω | ∀ j < k, S_from 0 (j + 1) ω ≤ 0} =
                ⋂ j ∈ Finset.range k, {ω | S_from 0 (j + 1) ω ≤ 0} := by ext ω; simp
            rw [hEq]
            exact measurableSet_biInter_finset_of_space mPast (Finset.range k)
              (fun j => {ω | S_from 0 (j + 1) ω ≤ 0}) fun j hj =>
                measurableSet_le_const_of_space mPast _ 0 (hS_past (j + 1) (by
                  have := Finset.mem_range.mp hj; omega))
          exact h1.inter (measurableSet_const_lt_of_space mPast 0 _ (hS_past (k + 1) le_rfl))
        have hf1_past : @Measurable Ω ℂ mPast _ f1 :=
          (Complex.continuous_exp.measurable.comp
            ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
              (hS_past (k + 1) le_rfl))).mul measurable_const)).indicator hEk_past
        have hf2_tail : @Measurable Ω ℂ
            (⨆ i ∈ {idx : ℕ ⊕ ℕ | k + 1 ≤ Sum.elim id id idx},
              MeasurableSpace.comap (Sum.elim arrival claims i) inferInstance) _ f2 :=
          Complex.continuous_exp.measurable.comp
            ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp
              (hM_meas_tail (k + 1)))).mul measurable_const)
        exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind hf1_past.comap_le)
          hf2_tail.comap_le
      have hMul := hInd_k.integral_fun_mul_eq_mul_integral
        hf1_meas.aestronglyMeasurable hf2_meas.aestronglyMeasurable
      have hL : (∫ ω in E k, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) =
          ∫ ω, f1 ω * f2 ω ∂P := by
        rw [← integral_indicator (hE_meas k)]
        refine integral_congr_ae ?_
        filter_upwards [hGood_ruin] with ω hω
        by_cases hk : ω ∈ E k
        · rw [Set.indicator_of_mem hk]
          dsimp only [f1, f2]
          rw [Set.indicator_of_mem hk, (hω.2.2 k hk).2, ← Complex.exp_add]
          congr 1; push_cast; ring
        · rw [Set.indicator_of_notMem hk]
          dsimp only [f1]; rw [Set.indicator_of_notMem hk, zero_mul]
      have hR1 : (∫ ω, f1 ω ∂P) =
          ∫ ω in E k, Complex.exp ((ξ : ℂ) * (S_from 0 (k + 1) ω : ℂ) * Complex.I) ∂P :=
        integral_indicator (hE_meas k)
      have hR2 : (∫ ω, f2 ω ∂P) = charFun (P.map (M_from 0)) ξ := by
        rw [← hM_law_eq (k + 1), charFun_apply_real]
        exact (integral_map (μ := P) (φ := M_from (k + 1))
          (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
          (hM_meas (k + 1)).aemeasurable (by fun_prop)).symm
      rw [hL, hMul, hR1, hR2]
    -- Sum over k and add the complement Uᶜ (where M_from 0 = 0 a.e.)
    have hExp_int : Integrable (fun ω => Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I)) P := by
      refine (integrable_const (1 : ℝ)).mono'
        (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp (hM_meas 0))).mul
            measurable_const)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      have harg : (ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I = ((ξ * M_from 0 ω : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    have hH1_int : Integrable (fun ω => Complex.exp ((ξ : ℂ) * (H1 ω : ℂ) * Complex.I)) (P.restrict U) := by
      refine (integrable_const (1 : ℝ)).mono'
        (Complex.continuous_exp.measurable.comp
          ((measurable_const.mul (Complex.continuous_ofReal.measurable.comp hH1_meas)).mul
            measurable_const)).aestronglyMeasurable ?_
      refine Filter.Eventually.of_forall fun ω => ?_
      have harg : (ξ : ℂ) * (H1 ω : ℂ) * Complex.I = ((ξ * H1 ω : ℝ) : ℂ) * Complex.I := by
        push_cast; ring
      rw [harg, Complex.norm_exp_ofReal_mul_I]
    have hSplit_M : charFun (P.map (M_from 0)) ξ =
        (∫ ω in Uᶜ, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) +
        (∫ ω in U, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) := by
      rw [charFun_apply_real, integral_map (μ := P) (φ := M_from 0)
        (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
        (hM_meas 0).aemeasurable (by fun_prop)]
      rw [← integral_add_compl hU_meas hExp_int, add_comm]
    have hCompl_val : (∫ ω in Uᶜ, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) =
        ((1 - ρ : ℝ) : ℂ) := by
      have hAe0 : ∀ᵐ ω ∂(P.restrict Uᶜ), Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) = 1 := by
        rw [ae_restrict_iff' hU_meas.compl]
        filter_upwards [hGood_ruin] with ω hω hnotU
        have hnotR : ω ∉ ruinEvent arrival claims premium 0 := fun hR =>
          hnotU (Set.mem_iUnion.mpr (hω.1.mp hR))
        have hM0 : M_from 0 ω = 0 :=
          le_antisymm (not_lt.mp (mt hω.2.1.mpr hnotR)) (hM_nonneg 0 ω)
        simp [hM0]
      rw [integral_congr_ae hAe0, setIntegral_const, Complex.real_smul, mul_one, Measure.real]
      have hPUc : (P Uᶜ).toReal = 1 - ρ := by
        have hPU : (P U).toReal = ρ := by
          rw [← measure_congr hRuin_eq_U]; exact hRuin0_prob
        rw [prob_compl_eq_one_sub hU_meas,
          ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_one, hPU]
      rw [hPUc]
    have hU_val : (∫ ω in U, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) =
        charFun ((P.restrict U).map H1) ξ * charFun (P.map (M_from 0)) ξ := by
      rw [integral_iUnion hE_meas hE_disj hExp_int.integrableOn]
      simp_rw [hM_term]
      rw [tsum_mul_right]
      congr 1
      rw [charFun_apply_real, integral_map (μ := P.restrict U) (φ := H1)
        (f := fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
        hH1_meas.aemeasurable (by fun_prop)]
      rw [integral_iUnion hE_meas hE_disj hH1_int]
      refine tsum_congr fun k => ?_
      refine setIntegral_congr_ae (hE_meas k) ?_
      filter_upwards [hH1_eq] with ω hω hk
      rw [hω k hk]
    have hEq_M : charFun (P.map (M_from 0)) ξ =
        ((1 - ρ : ℝ) : ℂ) + charFun ((P.restrict U).map H1) ξ * charFun (P.map (M_from 0)) ξ := by
      calc charFun (P.map (M_from 0)) ξ
          = (∫ ω in Uᶜ, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) +
            (∫ ω in U, Complex.exp ((ξ : ℂ) * (M_from 0 ω : ℂ) * Complex.I) ∂P) := hSplit_M
        _ = ((1 - ρ : ℝ) : ℂ) + charFun ((P.restrict U).map H1) ξ * charFun (P.map (M_from 0)) ξ := by
            rw [hCompl_val, hU_val]
    have hcfM_ne : charFun (P.map (M_from 0)) ξ ≠ 0 := by
      intro h0
      have hfac := hFactor_all ξ
      rw [h0, zero_mul] at hfac
      have : (1 - ρ : ℝ) = 0 := by exact_mod_cast hfac.symm
      linarith
    have hcf_H1 : charFun ((P.restrict U).map H1) ξ = (ρ : ℂ) * charFun eta ξ := by
      have h1 : charFun ((P.restrict U).map H1) ξ * charFun (P.map (M_from 0)) ξ =
          ((ρ : ℂ) * charFun eta ξ) * charFun (P.map (M_from 0)) ξ := by
        have hfac := hFactor_all ξ
        linear_combination hEq_M.symm + hfac
      exact mul_right_cancel₀ hcfM_ne h1
    rw [hcf_H1, charFun_apply_real, charFun_apply_real, integral_smul_measure,
      ENNReal.toReal_ofReal hρ_pos.le, Complex.real_smul]
  have : IsFiniteMeasure (ENNReal.ofReal ρ • eta) :=
    ⟨by simp [ENNReal.ofReal_lt_top]⟩
  have hMap_eq : (P.restrict U).map H1 = ENNReal.ofReal ρ • eta :=
    Measure.ext_of_charFun (funext hLadder_cf)
  refine ⟨hRuin0_prob, fun x hx => ?_⟩
  have hSet_eq : (ruinEvent arrival claims premium 0 ∩
      {ω | ruinDeficit arrival claims premium 0 ω ≤ x} : Set Ω) =ᵐ[P]
      (U ∩ {ω | H1 ω ≤ x} : Set Ω) := by
    filter_upwards [hGood_ruin, hH1_eq] with ω hω hH1ω
    change (ω ∈ ruinEvent arrival claims premium 0 ∧ ruinDeficit arrival claims premium 0 ω ≤ x) =
      (ω ∈ U ∧ H1 ω ≤ x)
    apply propext
    constructor
    · rintro ⟨hR, hle⟩
      obtain ⟨k, hk⟩ := hω.1.mp hR
      refine ⟨Set.mem_iUnion.mpr ⟨k, hk⟩, ?_⟩
      rw [hH1ω k hk, ← (hω.2.2 k hk).1]
      exact hle
    · rintro ⟨hU, hle⟩
      obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hU
      refine ⟨hω.1.mpr ⟨k, hk⟩, ?_⟩
      rw [(hω.2.2 k hk).1, ← hH1ω k hk]
      exact hle
  rw [measure_congr hSet_eq, hRuin0_prob, ← hetaCDF x hx]
  have h1 : P (U ∩ {ω | H1 ω ≤ x}) = ((P.restrict U).map H1) (Set.Iic x) := by
    rw [Measure.map_apply hH1_meas measurableSet_Iic, Measure.restrict_apply (hH1_meas measurableSet_Iic)]
    exact congrArg P (Set.inter_comm _ _)
  rw [h1, hMap_eq, Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hρ_pos.le]
