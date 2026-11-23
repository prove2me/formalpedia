-- Prove2me | solution 1 for Kyprianou.Ch03.esscherDensity_densityTimeConsistency
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T19:04:34.202335+00:00
-- url     : https://prove2.me/submissions/d2cade13-098a-4ec9-a00f-f7ae483ce294

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_EsscherDensity
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration

open MeasureTheory ProbabilityTheory Complex Set Filter Topology
open scoped NNReal ENNReal Interval
set_option autoImplicit false

namespace EsscherTripletWitnessProp2Aux

/-! ### Elementary exponential remainder bounds -/

private lemma norm_cexp_sub_one_le (w : ℂ) :
    ‖Complex.exp w - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * w))
        (w * Complex.exp ((t : ℂ) * w)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) (1 * w) t :=
      (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1.cexp
  have hcont : Continuous (fun s : ℝ => w * Complex.exp ((s : ℂ) * w)) := by fun_prop
  have hftc : ∫ s in (0 : ℝ)..1, w * Complex.exp ((s : ℂ) * w) = Complex.exp w - 1 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
    simpa using this
  rw [← hftc]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖w * Complex.exp ((s : ℂ) * w)‖ ≤ ‖w‖ * Real.exp ‖w‖ := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [norm_mul, Complex.norm_exp]
    gcongr
    have hre : ((s : ℂ) * w).re ≤ ‖(s : ℂ) * w‖ := Complex.re_le_norm _
    refine hre.trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
    exact mul_le_of_le_one_left (norm_nonneg w) hs.2
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

private lemma norm_cexp_sub_one_sub_le (w : ℂ) :
    ‖Complex.exp w - 1 - w‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
  have hderiv : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun s : ℝ => Complex.exp ((s : ℂ) * w) - (s : ℂ) * w)
        (w * (Complex.exp ((t : ℂ) * w) - 1)) t := by
    intro t _
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ) * w) (1 * w) t :=
      (Complex.ofRealCLM.hasDerivAt (x := t)).mul_const w
    have h2 := h1.cexp.sub h1
    exact h2.congr_deriv (by ring)
  have hcont : Continuous (fun s : ℝ => w * (Complex.exp ((s : ℂ) * w) - 1)) := by fun_prop
  have hftc : ∫ s in (0 : ℝ)..1, w * (Complex.exp ((s : ℂ) * w) - 1) =
      Complex.exp w - 1 - w := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable 0 1)
    simpa [sub_sub, add_comm, add_left_comm, add_assoc] using this
  rw [← hftc]
  have hbound : ∀ s ∈ Set.uIoc (0 : ℝ) 1,
      ‖w * (Complex.exp ((s : ℂ) * w) - 1)‖ ≤ ‖w‖ ^ 2 * Real.exp ‖w‖ := by
    intro s hs
    rw [Set.uIoc_of_le zero_le_one] at hs
    rw [norm_mul]
    have hstep := norm_cexp_sub_one_le ((s : ℂ) * w)
    have hnorm : ‖(s : ℂ) * w‖ ≤ ‖w‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hs.1]
      exact mul_le_of_le_one_left (norm_nonneg w) hs.2
    have hstep2 : ‖Complex.exp ((s : ℂ) * w) - 1‖ ≤ ‖w‖ * Real.exp ‖w‖ :=
      hstep.trans (mul_le_mul hnorm (Real.exp_le_exp.mpr hnorm) (Real.exp_nonneg _) (norm_nonneg w))
    calc ‖w‖ * ‖Complex.exp ((s : ℂ) * w) - 1‖
        ≤ ‖w‖ * (‖w‖ * Real.exp ‖w‖) := mul_le_mul_of_nonneg_left hstep2 (norm_nonneg w)
      _ = ‖w‖ ^ 2 * Real.exp ‖w‖ := by ring
  simpa using intervalIntegral.norm_integral_le_of_norm_le_const hbound

private lemma real_exp_mul_le_one_add_exp {β r x : ℝ}
    (hr1 : min 0 β ≤ r) (hr2 : r ≤ max 0 β) :
    Real.exp (r * x) ≤ 1 + Real.exp (β * x) := by
  have hor : r * x ≤ 0 ∨ r * x ≤ β * x := by
    rcases le_total 0 β with hβ | hβ
    · rw [min_eq_left hβ] at hr1
      rw [max_eq_right hβ] at hr2
      rcases le_total 0 x with hx | hx
      · exact Or.inr (mul_le_mul_of_nonneg_right hr2 hx)
      · exact Or.inl (mul_nonpos_of_nonneg_of_nonpos hr1 hx)
    · rw [min_eq_right hβ] at hr1
      rw [max_eq_left hβ] at hr2
      rcases le_total 0 x with hx | hx
      · exact Or.inl (mul_nonpos_of_nonpos_of_nonneg hr2 hx)
      · exact Or.inr (mul_le_mul_of_nonpos_right hr1 hx)
  rcases hor with h | h
  · have h1 : Real.exp (r * x) ≤ 1 := by simpa using Real.exp_le_exp.mpr h
    linarith [Real.exp_pos (β * x)]
  · have h2 : Real.exp (r * x) ≤ Real.exp (β * x) := Real.exp_le_exp.mpr h
    linarith

private lemma abs_mul_exp_le_of_margin {β r δ x : ℝ} (hδ : 0 < δ)
    (hr1 : min 0 β + δ ≤ r) (hr2 : r ≤ max 0 β - δ) :
    |x| * Real.exp (r * x) ≤ (1 / δ) * (1 + Real.exp (β * x)) := by
  have h1 : ∀ u : ℝ, 0 ≤ u → u ≤ Real.exp u := fun u _ => by linarith [Real.add_one_le_exp u]
  rcases le_total 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    have hdx : δ * x ≤ Real.exp (δ * x) := h1 (δ * x) (mul_nonneg hδ.le hx)
    have hmul : x * Real.exp (r * x) ≤ (1 / δ) * Real.exp ((r + δ) * x) := by
      rw [one_div]
      have h' : δ * (x * Real.exp (r * x)) ≤ Real.exp ((r + δ) * x) := by
        calc δ * (x * Real.exp (r * x))
            = (δ * x) * Real.exp (r * x) := by ring
          _ ≤ Real.exp (δ * x) * Real.exp (r * x) :=
              mul_le_mul_of_nonneg_right hdx (Real.exp_nonneg _)
          _ = Real.exp ((r + δ) * x) := by rw [← Real.exp_add]; ring_nf
      exact (le_inv_mul_iff₀ hδ).mpr h'
    refine hmul.trans ?_
    gcongr
    exact real_exp_mul_le_one_add_exp (by linarith) (by linarith)
  · rw [abs_of_nonpos hx]
    have hdx : δ * (-x) ≤ Real.exp (δ * (-x)) := h1 (δ * (-x)) (mul_nonneg hδ.le (neg_nonneg.mpr hx))
    have hmul : (-x) * Real.exp (r * x) ≤ (1 / δ) * Real.exp ((r - δ) * x) := by
      rw [one_div]
      have h' : δ * ((-x) * Real.exp (r * x)) ≤ Real.exp ((r - δ) * x) := by
        calc δ * ((-x) * Real.exp (r * x))
            = (δ * (-x)) * Real.exp (r * x) := by ring
          _ ≤ Real.exp (δ * (-x)) * Real.exp (r * x) :=
              mul_le_mul_of_nonneg_right hdx (Real.exp_nonneg _)
          _ = Real.exp ((r - δ) * x) := by rw [← Real.exp_add]; ring_nf
      exact (le_inv_mul_iff₀ hδ).mpr h'
    refine hmul.trans ?_
    gcongr
    exact real_exp_mul_le_one_add_exp (by linarith) (by linarith)

/-! ### Complex-analytic extension of the Lévy–Khintchine exponent -/

private noncomputable def expCompIntegrand (z : ℂ) (x : ℝ) : ℂ :=
  Complex.exp (z * (x : ℂ)) - 1 - z * (x : ℂ) * if |x| < 1 then 1 else 0

private noncomputable def levyComplexExponent
    (T : ProbabilityTheory.LevyKhintchineTriple) (z : ℂ) : ℂ :=
  (T.drift : ℂ) * z + ((T.gaussianVariance : ℝ) : ℂ) * z ^ 2 / 2 +
    ∫ x, expCompIntegrand z x ∂T.levyMeasure

private lemma levyComplexExponent_I_mul
    (T : ProbabilityTheory.LevyKhintchineTriple) (ξ : ℝ) :
    levyComplexExponent T (I * (ξ : ℂ)) = Kyprianou.Ch01.levyTripleExponent T ξ := by
  unfold levyComplexExponent Kyprianou.Ch01.levyTripleExponent
  have hint : (fun x : ℝ => expCompIntegrand (I * (ξ : ℂ)) x) =
      fun x : ℝ => ProbabilityTheory.levyCompensatedIntegrand ξ x := by
    ext x
    unfold expCompIntegrand ProbabilityTheory.levyCompensatedIntegrand
    have h1 : I * (ξ : ℂ) * (x : ℂ) = (x : ℂ) * (ξ : ℂ) * I := by ring
    rw [h1]
  rw [hint]
  push_cast
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI2]
  ring

private lemma integrable_min_one_sq (T : ProbabilityTheory.LevyKhintchineTriple) :
    Integrable (fun x : ℝ => min (1 : ℝ) (x ^ 2)) T.levyMeasure := by
  have hmeas : Measurable (fun x : ℝ => min (1 : ℝ) (x ^ 2)) :=
    measurable_const.min (measurable_id.pow_const 2)
  refine ⟨hmeas.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x => le_min zero_le_one (sq_nonneg x))]
  exact T.levyMeasure_isLevyMeasure.2

private lemma integrableOn_const_large (T : ProbabilityTheory.LevyKhintchineTriple) (C : ℝ) :
    IntegrableOn (fun _ : ℝ => C) {x : ℝ | 1 ≤ |x|} T.levyMeasure :=
  integrableOn_const (hs := (T.levyMeasure_isLevyMeasure.measure_setOf_abs_ge_lt_top zero_lt_one).ne)

private lemma integrable_strip_bound (T : ProbabilityTheory.LevyKhintchineTriple)
    {β C₁ C₂ C₃ : ℝ}
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    Integrable (fun x : ℝ =>
      if |x| < 1 then C₁ * min (1 : ℝ) (x ^ 2) else C₂ + C₃ * Real.exp (β * x)) T.levyMeasure := by
  have hmeas_lt : MeasurableSet {x : ℝ | |x| < 1} := measurableSet_lt measurable_abs measurable_const
  have hmeas_ge : MeasurableSet {x : ℝ | 1 ≤ |x|} := measurableSet_le measurable_const measurable_abs
  have h1 : IntegrableOn (fun x : ℝ => C₁ * min (1 : ℝ) (x ^ 2)) {x : ℝ | |x| < 1} T.levyMeasure :=
    ((integrable_min_one_sq T).const_mul C₁).integrableOn
  have h2 : IntegrableOn (fun x : ℝ => C₂ + C₃ * Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure :=
    (integrableOn_const_large T C₂).add (hBeta.const_mul C₃)
  have hcompl : {x : ℝ | |x| < 1}ᶜ = {x : ℝ | 1 ≤ |x|} := by
    ext x; simp [not_lt]
  have hsum : Integrable
      (fun x : ℝ => Set.indicator {x : ℝ | |x| < 1} (fun x => C₁ * min (1 : ℝ) (x ^ 2)) x +
        Set.indicator {x : ℝ | 1 ≤ |x|} (fun x => C₂ + C₃ * Real.exp (β * x)) x) T.levyMeasure :=
    (h1.integrable_indicator hmeas_lt).add (h2.integrable_indicator hmeas_ge)
  refine hsum.congr (ae_of_all _ fun x => ?_)
  by_cases hx : |x| < 1
  · have hx' : ¬ (1 ≤ |x|) := not_le.mpr hx
    simp [Set.indicator, hx, hx']
  · have hx' : 1 ≤ |x| := not_lt.mp hx
    simp [Set.indicator, hx, hx']

private lemma measurable_expCompIntegrand (z : ℂ) :
    Measurable (expCompIntegrand z) := by
  unfold expCompIntegrand
  have h1 : Measurable (fun x : ℝ => Complex.exp (z * (x : ℂ)) - 1) := by fun_prop
  have h2 : Measurable (fun x : ℝ => z * (x : ℂ)) := by fun_prop
  have h3 : Measurable (fun x : ℝ => if |x| < 1 then (1 : ℂ) else 0) :=
    Measurable.ite (measurableSet_lt measurable_abs measurable_const) measurable_const measurable_const
  exact h1.sub (h2.mul h3)

private lemma norm_expCompIntegrand_le {β R : ℝ} {z : ℂ}
    (hr1 : min 0 β ≤ z.re) (hr2 : z.re ≤ max 0 β) (hzR : ‖z‖ ≤ R) (x : ℝ) :
    ‖expCompIntegrand z x‖ ≤
      if |x| < 1 then (R ^ 2 * Real.exp R) * min (1 : ℝ) (x ^ 2)
      else 2 + 1 * Real.exp (β * x) := by
  unfold expCompIntegrand
  by_cases hx : |x| < 1
  · simp only [hx, ↓reduceIte, mul_one]
    have hstep := norm_cexp_sub_one_sub_le (z * (x : ℂ))
    have hzx : ‖z * (x : ℂ)‖ = ‖z‖ * |x| := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hzx_le : ‖z * (x : ℂ)‖ ≤ R := by
      rw [hzx]
      calc ‖z‖ * |x| ≤ R * 1 := mul_le_mul hzR hx.le (abs_nonneg x) ((norm_nonneg z).trans hzR)
        _ = R := mul_one R
    have hsq_le : x ^ 2 ≤ 1 := by
      have : |x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx.le 2
      simpa [sq_abs] using this
    have hmin : min (1 : ℝ) (x ^ 2) = x ^ 2 := min_eq_right hsq_le
    rw [hmin]
    calc ‖Complex.exp (z * (x : ℂ)) - 1 - z * (x : ℂ)‖
        ≤ ‖z * (x : ℂ)‖ ^ 2 * Real.exp ‖z * (x : ℂ)‖ := hstep
      _ = (‖z‖ ^ 2 * Real.exp ‖z * (x : ℂ)‖) * x ^ 2 := by rw [hzx, mul_pow, sq_abs]; ring
      _ ≤ (R ^ 2 * Real.exp R) * x ^ 2 := by
          gcongr
  · simp only [hx, ↓reduceIte, mul_zero, sub_zero, one_mul]
    calc ‖Complex.exp (z * (x : ℂ)) - 1‖
        ≤ ‖Complex.exp (z * (x : ℂ))‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
      _ = Real.exp (z.re * x) + 1 := by simp [Complex.norm_exp]
      _ ≤ (1 + Real.exp (β * x)) + 1 := by linarith [real_exp_mul_le_one_add_exp hr1 hr2 (x := x)]
      _ = 2 + Real.exp (β * x) := by ring

private lemma integrable_expCompIntegrand
    (T : ProbabilityTheory.LevyKhintchineTriple) {β : ℝ}
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure)
    {z : ℂ} (hr1 : min 0 β ≤ z.re) (hr2 : z.re ≤ max 0 β) :
    Integrable (expCompIntegrand z) T.levyMeasure := by
  refine (integrable_strip_bound T hBeta (C₁ := ‖z‖ ^ 2 * Real.exp ‖z‖) (C₂ := 2) (C₃ := 1)).mono'
    (measurable_expCompIntegrand z).aestronglyMeasurable (ae_of_all _ fun x => ?_)
  exact norm_expCompIntegrand_le hr1 hr2 le_rfl x

private lemma integrableOn_drift_shift
    (T : ProbabilityTheory.LevyKhintchineTriple) (β : ℝ) :
    IntegrableOn (fun x : ℝ => (Real.exp (β * x) - 1) * x) {x : ℝ | |x| < 1} T.levyMeasure := by
  have hmeas : Measurable (fun x : ℝ => (Real.exp (β * x) - 1) * x) := by fun_prop
  refine ((integrable_min_one_sq T).const_mul (|β| * Real.exp |β|)).integrableOn.mono'
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_lt measurable_abs measurable_const)] with x hx
  have hx' : |x| < 1 := hx
  have hsq : x ^ 2 ≤ 1 := by
    have : |x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx'.le 2
    simpa [sq_abs] using this
  have h1 : ‖Real.exp (β * x) - 1‖ ≤ |β * x| * Real.exp |β * x| := by
    have h := norm_cexp_sub_one_le ((β * x : ℝ) : ℂ)
    have hcoe : Complex.exp ((β * x : ℝ) : ℂ) - 1 = ((Real.exp (β * x) - 1 : ℝ) : ℂ) := by
      push_cast; rfl
    rw [hcoe, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs] at h
    exact h
  have hbx : |β * x| ≤ |β| := by
    rw [abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg β) hx'.le
  rw [Real.norm_eq_abs, abs_mul, min_eq_right hsq]
  calc |Real.exp (β * x) - 1| * |x|
      ≤ (|β * x| * Real.exp |β * x|) * |x| := by
        rw [← Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right h1 (abs_nonneg x)
    _ = (|β| * Real.exp |β * x|) * x ^ 2 := by
        rw [abs_mul, show |β| * |x| * Real.exp (|β| * |x|) * |x| =
          (|β| * Real.exp (|β| * |x|)) * |x| ^ 2 by ring, sq_abs]
    _ ≤ (|β| * Real.exp |β|) * x ^ 2 := by gcongr

private lemma levyComplexExponent_shift
    (T Tbeta : ProbabilityTheory.LevyKhintchineTriple) {β : ℝ}
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure)
    (hDrift : Tbeta.drift = T.drift + β * (T.gaussianVariance : ℝ) +
      ∫ x in {x : ℝ | |x| < 1}, (Real.exp (β * x) - 1) * x ∂T.levyMeasure)
    (hVar : Tbeta.gaussianVariance = T.gaussianVariance)
    (hLevy : Tbeta.levyMeasure = T.levyMeasure.withDensity
      (fun x : ℝ => ENNReal.ofReal (Real.exp (β * x))))
    (ξ : ℝ) :
    levyComplexExponent T ((β : ℂ) + I * (ξ : ℂ)) - levyComplexExponent T (β : ℂ) =
      Kyprianou.Ch01.levyTripleExponent Tbeta ξ := by
  have hInt1 : Integrable (expCompIntegrand ((β : ℂ) + I * (ξ : ℂ))) T.levyMeasure :=
    integrable_expCompIntegrand T hBeta (by simp) (by simp)
  have hInt2 : Integrable (expCompIntegrand (β : ℂ)) T.levyMeasure :=
    integrable_expCompIntegrand T hBeta (by simp) (by simp)
  have hmeas_lt : MeasurableSet {x : ℝ | |x| < 1} := measurableSet_lt measurable_abs measurable_const
  have hIntShiftReal : Integrable
      (Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x)) T.levyMeasure :=
    (integrableOn_drift_shift T β).integrable_indicator hmeas_lt
  have hIntShiftC : Integrable
      (fun x : ℝ => I * (ξ : ℂ) *
        ((Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x) x : ℝ) : ℂ))
      T.levyMeasure :=
    (hIntShiftReal.ofReal).const_mul (I * (ξ : ℂ))
  have hpt : ∀ x : ℝ,
      expCompIntegrand ((β : ℂ) + I * (ξ : ℂ)) x - expCompIntegrand (β : ℂ) x =
        Real.exp (β * x) • ProbabilityTheory.levyCompensatedIntegrand ξ x +
        I * (ξ : ℂ) *
          ((Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x) x : ℝ) : ℂ) := by
    intro x
    unfold expCompIntegrand ProbabilityTheory.levyCompensatedIntegrand
    rw [Complex.real_smul, Complex.ofReal_exp]
    have hexp : Complex.exp (((β : ℂ) + I * (ξ : ℂ)) * (x : ℂ)) =
        Complex.exp ((β * x : ℝ) : ℂ) * Complex.exp ((x : ℂ) * (ξ : ℂ) * I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hexp]
    by_cases hx : |x| < 1
    · have hmem : x ∈ {x : ℝ | |x| < 1} := hx
      simp only [hx, ↓reduceIte, Set.indicator_of_mem hmem, mul_one]
      push_cast
      ring
    · have hnot : x ∉ {x : ℝ | |x| < 1} := hx
      simp only [hx, ↓reduceIte, Set.indicator_of_notMem hnot, mul_zero, sub_zero,
        Complex.ofReal_zero, add_zero]
      push_cast
      ring
  have hIntTilted : Integrable
      (fun x : ℝ => Real.exp (β * x) • ProbabilityTheory.levyCompensatedIntegrand ξ x)
      T.levyMeasure := by
    have hdiff := hInt1.sub hInt2
    have heq : (fun x : ℝ => Real.exp (β * x) • ProbabilityTheory.levyCompensatedIntegrand ξ x) =
        fun x : ℝ => (expCompIntegrand ((β : ℂ) + I * (ξ : ℂ)) x - expCompIntegrand (β : ℂ) x) -
          I * (ξ : ℂ) *
            ((Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x) x : ℝ) : ℂ) := by
      ext x; rw [hpt x]; ring
    rw [heq]
    exact hdiff.sub hIntShiftC
  have hint_eq :
      (∫ x, expCompIntegrand ((β : ℂ) + I * (ξ : ℂ)) x ∂T.levyMeasure) -
        (∫ x, expCompIntegrand (β : ℂ) x ∂T.levyMeasure) =
      (∫ x, ProbabilityTheory.levyCompensatedIntegrand ξ x ∂Tbeta.levyMeasure) +
        I * (ξ : ℂ) *
          ((∫ x in {x : ℝ | |x| < 1}, (Real.exp (β * x) - 1) * x ∂T.levyMeasure : ℝ) : ℂ) := by
    rw [← integral_sub hInt1 hInt2]
    simp_rw [hpt]
    rw [integral_add hIntTilted hIntShiftC]
    congr 1
    · rw [hLevy, integral_withDensity_eq_integral_toReal_smul
        (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (β * x))) by fun_prop)
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      congr 1
      ext x
      rw [ENNReal.toReal_ofReal (Real.exp_nonneg _)]
    · rw [integral_const_mul,
        show (∫ a, ((Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x) a : ℝ) : ℂ) ∂T.levyMeasure) =
          ((∫ a, Set.indicator {x : ℝ | |x| < 1} (fun x : ℝ => (Real.exp (β * x) - 1) * x) a ∂T.levyMeasure : ℝ) : ℂ) from
            Complex.ofRealCLM.integral_comp_comm hIntShiftReal,
        integral_indicator hmeas_lt]
  unfold levyComplexExponent Kyprianou.Ch01.levyTripleExponent
  rw [hDrift, hVar]
  have halg :
      ((T.drift : ℂ) * ((β : ℂ) + I * (ξ : ℂ)) +
          ((T.gaussianVariance : ℝ) : ℂ) * ((β : ℂ) + I * (ξ : ℂ)) ^ 2 / 2 +
          ∫ x, expCompIntegrand ((β : ℂ) + I * (ξ : ℂ)) x ∂T.levyMeasure) -
        ((T.drift : ℂ) * (β : ℂ) +
          ((T.gaussianVariance : ℝ) : ℂ) * (β : ℂ) ^ 2 / 2 +
          ∫ x, expCompIntegrand (β : ℂ) x ∂T.levyMeasure) =
      (T.drift : ℂ) * (I * (ξ : ℂ)) +
        ((T.gaussianVariance : ℝ) : ℂ) * (((β : ℂ) + I * (ξ : ℂ)) ^ 2 - (β : ℂ) ^ 2) / 2 +
        ((∫ x, expCompIntegrand ((β : ℂ) + I * (ξ : ℂ)) x ∂T.levyMeasure) -
          (∫ x, expCompIntegrand (β : ℂ) x ∂T.levyMeasure)) := by ring
  rw [halg, hint_eq]
  push_cast
  have hI2 : I ^ 2 = -1 := Complex.I_sq
  ring_nf
  rw [hI2]
  ring

private lemma levyComplexExponent_ofReal_im
    (T : ProbabilityTheory.LevyKhintchineTriple) (β : ℝ) :
    (levyComplexExponent T (β : ℂ)).im = 0 := by
  unfold levyComplexExponent
  have hint : (fun x : ℝ => expCompIntegrand (β : ℂ) x) =
      fun x : ℝ =>
        ((Real.exp (β * x) - 1 - β * x * if |x| < 1 then 1 else 0 : ℝ) : ℂ) := by
    ext x
    unfold expCompIntegrand
    by_cases hx : |x| < 1 <;> simp [hx, Complex.ofReal_exp]
  rw [hint]
  have hreal : (∫ x, ((Real.exp (β * x) - 1 - β * x * if |x| < 1 then 1 else 0 : ℝ) : ℂ) ∂T.levyMeasure) =
      ((∫ x, (Real.exp (β * x) - 1 - β * x * if |x| < 1 then 1 else 0 : ℝ) ∂T.levyMeasure : ℝ) : ℂ) :=
    integral_ofReal (𝕜 := ℂ)
  rw [hreal]
  simp [← Complex.ofReal_pow]

/-! ### Continuity and holomorphicity of `levyComplexExponent` on the strip -/

private lemma continuousOn_levyComplexExponent
    (T : ProbabilityTheory.LevyKhintchineTriple) {β : ℝ}
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    ContinuousOn (levyComplexExponent T) {z : ℂ | min 0 β ≤ z.re ∧ z.re ≤ max 0 β} := by
  unfold levyComplexExponent
  have hpoly : ContinuousOn
      (fun z : ℂ => (T.drift : ℂ) * z + ((T.gaussianVariance : ℝ) : ℂ) * z ^ 2 / 2)
      {z : ℂ | min 0 β ≤ z.re ∧ z.re ≤ max 0 β} := by fun_prop
  refine hpoly.add ?_
  intro z₀ hz₀
  set R : ℝ := ‖z₀‖ + 1
  have hcont_ball : ContinuousOn (fun z : ℂ => ∫ x, expCompIntegrand z x ∂T.levyMeasure)
      ({z : ℂ | min 0 β ≤ z.re ∧ z.re ≤ max 0 β} ∩ Metric.ball z₀ 1) := by
    refine continuousOn_of_dominated
      (bound := fun x : ℝ =>
        if |x| < 1 then (R ^ 2 * Real.exp R) * min (1 : ℝ) (x ^ 2)
        else 2 + 1 * Real.exp (β * x)) ?_ ?_ ?_ ?_
    · intro z _
      exact (measurable_expCompIntegrand z).aestronglyMeasurable
    · intro z hz
      refine ae_of_all _ fun x => norm_expCompIntegrand_le hz.1.1 hz.1.2 ?_ x
      have hdist : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz.2
      calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
        _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
        _ ≤ 1 + ‖z₀‖ := by linarith
        _ = R := by ring
    · exact integrable_strip_bound T hBeta
    · refine ae_of_all _ fun x => ?_
      unfold expCompIntegrand
      fun_prop
  have hmem : Metric.ball z₀ 1 ∈ 𝓝 z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
  exact (hcont_ball z₀ ⟨hz₀, Metric.mem_ball_self zero_lt_one⟩).mono_of_mem_nhdsWithin
    (inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds hmem))

private lemma differentiableOn_levyComplexExponent
    (T : ProbabilityTheory.LevyKhintchineTriple) {β : ℝ}
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    DifferentiableOn ℂ (levyComplexExponent T) {z : ℂ | min 0 β < z.re ∧ z.re < max 0 β} := by
  unfold levyComplexExponent
  have hpoly : DifferentiableOn ℂ
      (fun z : ℂ => (T.drift : ℂ) * z + ((T.gaussianVariance : ℝ) : ℂ) * z ^ 2 / 2)
      {z : ℂ | min 0 β < z.re ∧ z.re < max 0 β} := by fun_prop
  refine hpoly.add ?_
  intro z₀ hz₀
  set δ : ℝ := min 1 (min ((z₀.re - min 0 β) / 2) ((max 0 β - z₀.re) / 2))
  have hδ_pos : 0 < δ := by
    refine lt_min zero_lt_one (lt_min ?_ ?_) <;> linarith [hz₀.1, hz₀.2]
  have hδ_le1 : δ ≤ 1 := min_le_left _ _
  have hδ_left : min 0 β + 2 * δ ≤ z₀.re := by
    have : δ ≤ (z₀.re - min 0 β) / 2 := (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hδ_right : z₀.re ≤ max 0 β - 2 * δ := by
    have : δ ≤ (max 0 β - z₀.re) / 2 := (min_le_right _ _).trans (min_le_right _ _)
    linarith
  set R : ℝ := ‖z₀‖ + 1
  let F' : ℂ → ℝ → ℂ := fun z x =>
    (x : ℂ) * (Complex.exp (z * (x : ℂ)) - if |x| < 1 then 1 else 0)
  have hF'_meas : Measurable (F' z₀) := by
    dsimp only [F']
    have h1 : Measurable (fun x : ℝ => (x : ℂ)) := by fun_prop
    have h2 : Measurable (fun x : ℝ => Complex.exp (z₀ * (x : ℂ))) := by fun_prop
    have h3 : Measurable (fun x : ℝ => if |x| < 1 then (1 : ℂ) else 0) :=
      Measurable.ite (measurableSet_lt measurable_abs measurable_const) measurable_const measurable_const
    exact h1.mul (h2.sub h3)
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z₀ δ) (x₀ := z₀) (F := expCompIntegrand) (F' := F')
    (bound := fun x : ℝ =>
      if |x| < 1 then (R * Real.exp R) * min (1 : ℝ) (x ^ 2)
      else (1 / δ) + (1 / δ) * Real.exp (β * x))
    (Metric.ball_mem_nhds z₀ hδ_pos)
    (Eventually.of_forall fun z => (measurable_expCompIntegrand z).aestronglyMeasurable)
    (integrable_expCompIntegrand T hBeta hz₀.1.le hz₀.2.le)
    hF'_meas.aestronglyMeasurable
    (ae_of_all _ fun x z hz => by
      have hdist : ‖z - z₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hre_diff : |z.re - z₀.re| < δ := by
        calc |z.re - z₀.re| = |(z - z₀).re| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          _ < δ := hdist
      have hr1 : min 0 β + δ ≤ z.re := by linarith [(abs_lt.mp hre_diff).1]
      have hr2 : z.re ≤ max 0 β - δ := by linarith [(abs_lt.mp hre_diff).2]
      have hzR : ‖z‖ ≤ R := by
        calc ‖z‖ = ‖(z - z₀) + z₀‖ := by ring_nf
          _ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_add_le _ _
          _ ≤ 1 + ‖z₀‖ := by linarith
          _ = R := by ring
      dsimp only [F']
      by_cases hx : |x| < 1
      · simp only [hx, ↓reduceIte]
        have hsq : x ^ 2 ≤ 1 := by
          have : |x| ^ 2 ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg x) hx.le 2
          simpa [sq_abs] using this
        rw [min_eq_right hsq, norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hstep := norm_cexp_sub_one_le (z * (x : ℂ))
        have hzx : ‖z * (x : ℂ)‖ = ‖z‖ * |x| := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        have hzx_le : ‖z * (x : ℂ)‖ ≤ R := by
          rw [hzx]
          calc ‖z‖ * |x| ≤ R * 1 := mul_le_mul hzR hx.le (abs_nonneg x) ((norm_nonneg z).trans hzR)
            _ = R := mul_one R
        calc |x| * ‖Complex.exp (z * (x : ℂ)) - 1‖
            ≤ |x| * (‖z * (x : ℂ)‖ * Real.exp ‖z * (x : ℂ)‖) :=
              mul_le_mul_of_nonneg_left hstep (abs_nonneg x)
          _ = (‖z‖ * Real.exp ‖z * (x : ℂ)‖) * x ^ 2 := by
              rw [hzx, show |x| * (‖z‖ * |x| * Real.exp (‖z‖ * |x|)) =
                (‖z‖ * Real.exp (‖z‖ * |x|)) * |x| ^ 2 by ring, sq_abs]
          _ ≤ (R * Real.exp R) * x ^ 2 := by gcongr
      · simp only [hx, ↓reduceIte, sub_zero]
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
        have hbound := abs_mul_exp_le_of_margin hδ_pos hr1 hr2 (x := x)
        have hre : (z * (x : ℂ)).re = z.re * x := by simp
        rw [hre]
        linarith)
    (integrable_strip_bound T hBeta)
    (ae_of_all _ fun x z _ => by
      dsimp only [expCompIntegrand, F']
      have h1 : HasDerivAt (fun w : ℂ => w * (x : ℂ)) (1 * (x : ℂ)) z :=
        (hasDerivAt_id z).mul_const (x : ℂ)
      have h2 := ((h1.cexp.sub_const 1).sub
        (h1.mul_const (if |x| < 1 then (1 : ℂ) else 0)))
      exact h2.congr_deriv (by ring))
  exact hderiv.2.differentiableAt.differentiableWithinAt

/-! ### Continuity and holomorphicity of the bilateral Laplace transform on the strip -/

private lemma continuousOn_bilateralLaplace
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β : ℝ}
    (hInt : Integrable (fun x : ℝ => Real.exp (β * x)) μ) :
    ContinuousOn (fun z : ℂ => ∫ x, Complex.exp (z * (x : ℂ)) ∂μ)
      {z : ℂ | min 0 β ≤ z.re ∧ z.re ≤ max 0 β} := by
  refine continuousOn_of_dominated (bound := fun x : ℝ => 1 + Real.exp (β * x)) ?_ ?_ ?_ ?_
  · intro z _
    exact (by fun_prop : Measurable (fun x : ℝ => Complex.exp (z * (x : ℂ)))).aestronglyMeasurable
  · intro z hz
    refine ae_of_all _ fun x => ?_
    rw [Complex.norm_exp]
    have hre : (z * (x : ℂ)).re = z.re * x := by simp
    rw [hre]
    exact real_exp_mul_le_one_add_exp hz.1 hz.2
  · exact (integrable_const (1 : ℝ)).add hInt
  · refine ae_of_all _ fun x => ?_
    fun_prop

private lemma differentiableOn_bilateralLaplace
    {μ : Measure ℝ} [IsProbabilityMeasure μ] {β : ℝ}
    (hInt : Integrable (fun x : ℝ => Real.exp (β * x)) μ) :
    DifferentiableOn ℂ (fun z : ℂ => ∫ x, Complex.exp (z * (x : ℂ)) ∂μ)
      {z : ℂ | min 0 β < z.re ∧ z.re < max 0 β} := by
  intro z₀ hz₀
  set δ : ℝ := min ((z₀.re - min 0 β) / 2) ((max 0 β - z₀.re) / 2)
  have hδ_pos : 0 < δ := lt_min (by linarith [hz₀.1]) (by linarith [hz₀.2])
  have hδ_left : min 0 β + 2 * δ ≤ z₀.re := by linarith [min_le_left ((z₀.re - min 0 β) / 2) ((max 0 β - z₀.re) / 2)]
  have hδ_right : z₀.re ≤ max 0 β - 2 * δ := by linarith [min_le_right ((z₀.re - min 0 β) / 2) ((max 0 β - z₀.re) / 2)]
  have hInt0 : Integrable (fun x : ℝ => Complex.exp (z₀ * (x : ℂ))) μ := by
    refine ((integrable_const (1 : ℝ)).add hInt).mono'
      (by fun_prop : Measurable (fun x : ℝ => Complex.exp (z₀ * (x : ℂ)))).aestronglyMeasurable
      (ae_of_all _ fun x => ?_)
    rw [Complex.norm_exp]
    have hre : (z₀ * (x : ℂ)).re = z₀.re * x := by simp
    rw [hre]
    exact real_exp_mul_le_one_add_exp hz₀.1.le hz₀.2.le
  have hderiv := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (s := Metric.ball z₀ δ) (x₀ := z₀)
    (F := fun z x => Complex.exp (z * (x : ℂ)))
    (F' := fun z x => (x : ℂ) * Complex.exp (z * (x : ℂ)))
    (bound := fun x : ℝ => (1 / δ) * (1 + Real.exp (β * x)))
    (Metric.ball_mem_nhds z₀ hδ_pos)
    (Eventually.of_forall fun z =>
      (by fun_prop : Measurable (fun x : ℝ => Complex.exp (z * (x : ℂ)))).aestronglyMeasurable)
    hInt0
    (by fun_prop : Measurable (fun x : ℝ => (x : ℂ) * Complex.exp (z₀ * (x : ℂ)))).aestronglyMeasurable
    (ae_of_all _ fun x z hz => by
      have hdist : ‖z - z₀‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hz
      have hre_diff : |z.re - z₀.re| < δ := by
        calc |z.re - z₀.re| = |(z - z₀).re| := by simp
          _ ≤ ‖z - z₀‖ := Complex.abs_re_le_norm _
          _ < δ := hdist
      have hr1 : min 0 β + δ ≤ z.re := by linarith [(abs_lt.mp hre_diff).1]
      have hr2 : z.re ≤ max 0 β - δ := by linarith [(abs_lt.mp hre_diff).2]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have hre : (z * (x : ℂ)).re = z.re * x := by simp
      rw [hre]
      exact abs_mul_exp_le_of_margin hδ_pos hr1 hr2)
    (((integrable_const (1 : ℝ)).add hInt).const_mul (1 / δ))
    (ae_of_all _ fun x z _ => by
      have h1 : HasDerivAt (fun w : ℂ => w * (x : ℂ)) (1 * (x : ℂ)) z :=
        (hasDerivAt_id z).mul_const (x : ℂ)
      exact h1.cexp.congr_deriv (by ring))
  exact hderiv.2.differentiableAt.differentiableWithinAt

/-! ### Boundary uniqueness on a vertical strip via Morera / antiderivative -/

private lemma rect_boundary_eq_zero_half_ext
    {H : ℂ → ℂ} {β : ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn H {z : ℂ | 0 ≤ z.re ∧ z.re ≤ β})
    (hdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.re ∧ z.re < β})
    (hzero : ∀ y : ℝ, H (y * I) = 0) :
    let H' : ℂ → ℂ := fun z => if 0 ≤ z.re then H z else 0
    ∀ (z w : ℂ), -β < z.re → z.re < β → -β < w.re → w.re < β →
      (∫ x : ℝ in z.re..w.re, H' (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, H' (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, H' (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, H' (z.re + y * I)) = 0 := by
  intro H'
  have hH'_nonneg : ∀ u : ℂ, 0 ≤ u.re → H' u = H u := fun u hu => by simp [H', hu]
  have hH'_nonpos : ∀ u : ℂ, u.re ≤ 0 → H' u = 0 := by
    intro u hu
    by_cases h0 : 0 ≤ u.re
    · have hre : u.re = 0 := le_antisymm hu h0
      have hu_eq : u = u.im * I := by apply Complex.ext <;> simp [hre]
      rw [hH'_nonneg u h0, hu_eq, hzero]
    · simp [H', h0]
  have hcase_pos : ∀ (z w : ℂ), 0 ≤ z.re → z.re < β → 0 ≤ w.re → w.re < β →
      (∫ x : ℝ in z.re..w.re, H' (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, H' (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, H' (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, H' (z.re + y * I)) = 0 := by
    intro z w hz1 hz2 hw1 hw2
    have heq_x : ∀ (c : ℝ),
        (∫ x : ℝ in z.re..w.re, H' (x + c * I)) = ∫ x : ℝ in z.re..w.re, H (x + c * I) := by
      intro c
      refine intervalIntegral.integral_congr fun x hx => ?_
      rw [Set.uIcc] at hx
      have hx0 : 0 ≤ x := (le_min hz1 hw1).trans hx.1
      exact hH'_nonneg _ (by simpa using hx0)
    have heq_y : ∀ (a : ℝ), 0 ≤ a →
        (∫ y : ℝ in z.im..w.im, H' (a + y * I)) = ∫ y : ℝ in z.im..w.im, H (a + y * I) := by
      intro a ha
      refine intervalIntegral.integral_congr fun y _ => hH'_nonneg _ (by simpa using ha)
    rw [heq_x, heq_x, heq_y w.re hw1, heq_y z.re hz1]
    refine Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn H z w ?_ ?_
    · refine hcont.mono fun u hu => ?_
      exact ⟨(le_min hz1 hw1).trans hu.1.1, hu.1.2.trans (max_le hz2.le hw2.le)⟩
    · refine hdiff.mono fun u hu => ?_
      exact ⟨(le_min hz1 hw1).trans_lt hu.1.1, hu.1.2.trans_le (max_le hz2.le hw2.le)⟩
  have hcase_neg : ∀ (z w : ℂ), z.re ≤ 0 → w.re ≤ 0 →
      (∫ x : ℝ in z.re..w.re, H' (x + z.im * I)) -
      (∫ x : ℝ in z.re..w.re, H' (x + w.im * I)) +
      I • (∫ y : ℝ in z.im..w.im, H' (w.re + y * I)) -
      I • (∫ y : ℝ in z.im..w.im, H' (z.re + y * I)) = 0 := by
    intro z w hz hw
    have hx0 : ∀ (c : ℝ), (∫ x : ℝ in z.re..w.re, H' (x + c * I)) = 0 := by
      intro c
      rw [intervalIntegral.integral_congr fun x hx => ?_, intervalIntegral.integral_zero]
      rw [Set.uIcc] at hx
      exact hH'_nonpos _ (by simpa using hx.2.trans (max_le hz hw))
    have hy0 : ∀ (a : ℝ), a ≤ 0 → (∫ y : ℝ in z.im..w.im, H' (a + y * I)) = 0 := by
      intro a ha
      rw [intervalIntegral.integral_congr fun y _ => hH'_nonpos _ (by simpa using ha),
        intervalIntegral.integral_zero]
    rw [hx0, hx0, hy0 w.re hw, hy0 z.re hz]
    simp
  have hH'_cont : ContinuousOn H' {z : ℂ | -β < z.re ∧ z.re < β} := by
    intro z hz
    rcases lt_trichotomy z.re 0 with hlt | heq | hgt
    · have hopen : {u : ℂ | u.re < 0} ∈ 𝓝 z :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt
      have heq_nhds : H' =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen] with u hu
        exact hH'_nonpos u hu.le
      exact (continuousAt_const.congr heq_nhds.symm).continuousWithinAt
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hz_mem : z ∈ {u : ℂ | 0 ≤ u.re ∧ u.re ≤ β} := ⟨heq.symm.le, by linarith⟩
      have hHz : H' z = 0 := hH'_nonpos z heq.le
      have hHz0 : H z = 0 := by rw [← hH'_nonneg z heq.symm.le, hHz]
      rcases (Metric.continuousWithinAt_iff.mp (hcont z hz_mem)) ε hε with ⟨δ, hδ, hball⟩
      refine ⟨min δ (β - z.re), lt_min hδ (by linarith), fun u hu hdist => ?_⟩
      rw [hHz, dist_zero_right]
      by_cases hu0 : 0 ≤ u.re
      · rw [hH'_nonneg u hu0]
        have hu_mem : u ∈ {u : ℂ | 0 ≤ u.re ∧ u.re ≤ β} := ⟨hu0, hu.2.le⟩
        have h := hball hu_mem (lt_of_lt_of_le hdist (min_le_left _ _))
        rwa [hHz0, dist_zero_right] at h
      · rw [hH'_nonpos u (le_of_not_ge hu0), norm_zero]
        exact hε
    · have hopen : {u : ℂ | 0 < u.re ∧ u.re < β} ∈ 𝓝 z :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hgt, hz.2⟩
      have hcont_at : ContinuousAt H z :=
        (hcont z ⟨hgt.le, hz.2.le⟩).continuousAt
          (Filter.mem_of_superset hopen fun u hu => ⟨hu.1.le, hu.2.le⟩)
      have heq_nhds : H' =ᶠ[𝓝 z] H := by
        filter_upwards [hopen] with u hu
        exact hH'_nonneg u hu.1.le
      exact (hcont_at.congr heq_nhds.symm).continuousWithinAt
  intro z w hz1 hz2 hw1 hw2
  have hint_x : ∀ (a b c : ℝ), -β < a → a < β → -β < b → b < β →
      IntervalIntegrable (fun x : ℝ => H' (x + c * I)) volume a b := by
    intro a b c ha1 ha2 hb1 hb2
    refine ContinuousOn.intervalIntegrable ?_
    have hcomp : ContinuousOn (fun x : ℝ => (x : ℂ) + (c : ℂ) * I) (Set.uIcc a b) := by fun_prop
    refine hH'_cont.comp hcomp fun x hx => ?_
    rw [Set.uIcc] at hx
    simp only [Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
      mul_one, sub_self, add_zero]
    exact ⟨(lt_min ha1 hb1).trans_le hx.1, hx.2.trans_lt (max_lt ha2 hb2)⟩
  rcases le_total 0 z.re with hz0 | hz0 <;> rcases le_total 0 w.re with hw0 | hw0
  · exact hcase_pos z w hz0 hz2 hw0 hw2
  · have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_x z.re 0 z.im hz1 hz2 (by linarith) hβ)
      (hint_x 0 w.re z.im (by linarith) hβ hw1 hw2)).symm
    have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_x z.re 0 w.im hz1 hz2 (by linarith) hβ)
      (hint_x 0 w.re w.im (by linarith) hβ hw1 hw2)).symm
    have h1 := hcase_pos z (0 + w.im * I) hz0 hz2 (by simp) (by simpa using hβ)
    have h2 := hcase_neg (0 + z.im * I) w (by simp) hw0
    simp only [zero_add, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      mul_im, add_zero] at h1 h2
    rw [hsplit1, hsplit2]
    linear_combination h1 + h2
  · have hsplit1 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_x z.re 0 z.im hz1 hz2 (by linarith) hβ)
      (hint_x 0 w.re z.im (by linarith) hβ hw1 hw2)).symm
    have hsplit2 := (intervalIntegral.integral_add_adjacent_intervals
      (hint_x z.re 0 w.im hz1 hz2 (by linarith) hβ)
      (hint_x 0 w.re w.im (by linarith) hβ hw1 hw2)).symm
    have h1 := hcase_neg z (0 + w.im * I) hz0 (by simp)
    have h2 := hcase_pos (0 + z.im * I) w (by simp) (by simpa using hβ) hw0 hw2
    simp only [zero_add, mul_re, ofReal_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
      mul_im, add_zero] at h1 h2
    rw [hsplit1, hsplit2]
    linear_combination h1 + h2
  · exact hcase_neg z w hz0 hw0

private lemma eq_zero_on_closed_strip_of_eq_zero_on_imag_axis
    {H : ℂ → ℂ} {β : ℝ} (hβ : 0 < β)
    (hcont : ContinuousOn H {z : ℂ | 0 ≤ z.re ∧ z.re ≤ β})
    (hdiff : DifferentiableOn ℂ H {z : ℂ | 0 < z.re ∧ z.re < β})
    (hzero : ∀ y : ℝ, H (y * I) = 0) :
    ∀ z : ℂ, 0 ≤ z.re → z.re ≤ β → H z = 0 := by
  let U : Set ℂ := {z : ℂ | -β < z.re ∧ z.re < β}
  let H' : ℂ → ℂ := fun z => if 0 ≤ z.re then H z else 0
  have hU_open : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hH'_nonneg : ∀ u : ℂ, 0 ≤ u.re → H' u = H u := fun u hu => by simp [H', hu]
  have hH'_nonpos : ∀ u : ℂ, u.re ≤ 0 → H' u = 0 := by
    intro u hu
    by_cases h0 : 0 ≤ u.re
    · have hre : u.re = 0 := le_antisymm hu h0
      have hu_eq : u = u.im * I := by apply Complex.ext <;> simp [hre]
      rw [hH'_nonneg u h0, hu_eq, hzero]
    · simp [H', h0]
  have hH'_cont : ContinuousOn H' U := by
    intro z hz
    rcases lt_trichotomy z.re 0 with hlt | heq | hgt
    · have hopen : {u : ℂ | u.re < 0} ∈ 𝓝 z :=
        (isOpen_lt Complex.continuous_re continuous_const).mem_nhds hlt
      have heq_nhds : H' =ᶠ[𝓝 z] 0 := by
        filter_upwards [hopen] with u hu
        exact hH'_nonpos u hu.le
      exact (continuousAt_const.congr heq_nhds.symm).continuousWithinAt
    · rw [Metric.continuousWithinAt_iff]
      intro ε hε
      have hz_mem : z ∈ {u : ℂ | 0 ≤ u.re ∧ u.re ≤ β} := ⟨heq.symm.le, by linarith⟩
      have hHz : H' z = 0 := hH'_nonpos z heq.le
      have hHz0 : H z = 0 := by rw [← hH'_nonneg z heq.symm.le, hHz]
      rcases (Metric.continuousWithinAt_iff.mp (hcont z hz_mem)) ε hε with ⟨δ, hδ, hball⟩
      refine ⟨min δ (β - z.re), lt_min hδ (by linarith), fun u hu hdist => ?_⟩
      rw [hHz, dist_zero_right]
      by_cases hu0 : 0 ≤ u.re
      · rw [hH'_nonneg u hu0]
        have hu_mem : u ∈ {u : ℂ | 0 ≤ u.re ∧ u.re ≤ β} := ⟨hu0, hu.2.le⟩
        have h := hball hu_mem (lt_of_lt_of_le hdist (min_le_left _ _))
        rwa [hHz0, dist_zero_right] at h
      · rw [hH'_nonpos u (le_of_not_ge hu0), norm_zero]
        exact hε
    · have hopen : {u : ℂ | 0 < u.re ∧ u.re < β} ∈ 𝓝 z :=
        ((isOpen_lt continuous_const Complex.continuous_re).inter
          (isOpen_lt Complex.continuous_re continuous_const)).mem_nhds ⟨hgt, hz.2⟩
      have hcont_at : ContinuousAt H z :=
        (hcont z ⟨hgt.le, hz.2.le⟩).continuousAt
          (Filter.mem_of_superset hopen fun u hu => ⟨hu.1.le, hu.2.le⟩)
      have heq_nhds : H' =ᶠ[𝓝 z] H := by
        filter_upwards [hopen] with u hu
        exact hH'_nonneg u hu.1.le
      exact (hcont_at.congr heq_nhds.symm).continuousWithinAt
  have hrect := rect_boundary_eq_zero_half_ext hβ hcont hdiff hzero
  let A : ℂ → ℂ := fun z =>
    (∫ x : ℝ in (0 : ℝ)..z.re, H' (x : ℂ)) + I * (∫ y : ℝ in (0 : ℝ)..z.im, H' (z.re + y * I))
  have hA_deriv : ∀ z ∈ U, HasDerivAt A (H' z) z := by
    intro z hz
    rw [hasDerivAt_iff_isLittleO]
    rw [Asymptotics.isLittleO_iff]
    intro c hc
    have hcont_at : ContinuousAt H' z := hH'_cont.continuousAt (hU_open.mem_nhds hz)
    rcases (Metric.continuousAt_iff.mp hcont_at) (c / 2) (half_pos hc) with ⟨δ₁, hδ₁, hball⟩
    set δ : ℝ := min (δ₁ / 2) (min (z.re + β) (β - z.re))
    have hδ_pos : 0 < δ := lt_min (half_pos hδ₁) (lt_min (by linarith [hz.1]) (by linarith [hz.2]))
    filter_upwards [Metric.ball_mem_nhds z hδ_pos] with w hw
    have hw_dist : ‖w - z‖ < δ := by simpa [Metric.mem_ball, dist_eq_norm] using hw
    have hw_re_diff : |w.re - z.re| < δ := by
      calc |w.re - z.re| = |(w - z).re| := by simp
        _ ≤ ‖w - z‖ := Complex.abs_re_le_norm _
        _ < δ := hw_dist
    have hwU : w ∈ U := by
      have h1 : δ ≤ z.re + β := (min_le_right _ _).trans (min_le_left _ _)
      have h2 : δ ≤ β - z.re := (min_le_right _ _).trans (min_le_right _ _)
      exact ⟨by linarith [(abs_lt.mp hw_re_diff).1], by linarith [(abs_lt.mp hw_re_diff).2]⟩
    have hint_x : ∀ (a b d : ℝ), -β < a → a < β → -β < b → b < β →
        IntervalIntegrable (fun x : ℝ => H' (x + d * I)) volume a b := by
      intro a b d ha1 ha2 hb1 hb2
      refine ContinuousOn.intervalIntegrable ?_
      have hcomp : ContinuousOn (fun x : ℝ => (x : ℂ) + (d : ℂ) * I) (Set.uIcc a b) := by fun_prop
      refine hH'_cont.comp hcomp fun x hx => ?_
      rw [Set.uIcc] at hx
      simp only [U, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact ⟨(lt_min ha1 hb1).trans_le hx.1, hx.2.trans_lt (max_lt ha2 hb2)⟩
    have hint_y : ∀ (a c1 c2 : ℝ), -β < a → a < β →
        IntervalIntegrable (fun y : ℝ => H' (a + y * I)) volume c1 c2 := by
      intro a c1 c2 ha1 ha2
      refine ContinuousOn.intervalIntegrable ?_
      have hcomp : ContinuousOn (fun y : ℝ => (a : ℂ) + (y : ℂ) * I) (Set.uIcc c1 c2) := by fun_prop
      refine hH'_cont.comp hcomp fun y _ => ?_
      simp only [U, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
        mul_one, sub_self, add_zero]
      exact ⟨ha1, ha2⟩
    -- Use rectangle on [z.re, w.re] x [0, z.im]
    have hR := hrect (z.re : ℂ) ((w.re : ℂ) + (z.im : ℂ) * I)
      (by simpa using hz.1) (by simpa using hz.2)
      (by simpa using hwU.1) (by simpa using hwU.2)
    have hR' :
        (∫ x : ℝ in z.re..w.re, H' (x : ℂ)) -
        (∫ x : ℝ in z.re..w.re, H' (x + z.im * I)) +
        I * (∫ y : ℝ in (0 : ℝ)..z.im, H' (w.re + y * I)) -
        I * (∫ y : ℝ in (0 : ℝ)..z.im, H' (z.re + y * I)) = 0 := by
      simpa only [H', ofReal_re, ofReal_im, ofReal_zero, zero_mul, add_zero, zero_add, add_re,
        mul_re, I_re, mul_zero, I_im, mul_one, sub_self, add_im, mul_im, smul_eq_mul] using hR
    have hx_split :
        (∫ x : ℝ in (0 : ℝ)..w.re, H' (x : ℂ)) - (∫ x : ℝ in (0 : ℝ)..z.re, H' (x : ℂ)) =
        ∫ x : ℝ in z.re..w.re, H' (x : ℂ) := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (by simpa using hint_x 0 z.re 0 (by linarith) hβ hz.1 hz.2)
        (by simpa using hint_x z.re w.re 0 hz.1 hz.2 hwU.1 hwU.2)
      linear_combination -h
    have hy_split :
        (∫ y : ℝ in (0 : ℝ)..w.im, H' (w.re + y * I)) -
        (∫ y : ℝ in (0 : ℝ)..z.im, H' (w.re + y * I)) =
        ∫ y : ℝ in z.im..w.im, H' (w.re + y * I) := by
      have h := intervalIntegral.integral_add_adjacent_intervals
        (hint_y w.re 0 z.im hwU.1 hwU.2)
        (hint_y w.re z.im w.im hwU.1 hwU.2)
      linear_combination -h
    have hAdiff : A w - A z =
        (∫ x : ℝ in z.re..w.re, H' (x + z.im * I)) +
        I * (∫ y : ℝ in z.im..w.im, H' (w.re + y * I)) := by
      dsimp only [A]
      linear_combination hx_split + I * hy_split + hR'
    have hlin : (w - z) * H' z =
        (∫ _x : ℝ in z.re..w.re, H' z) + I * (∫ _y : ℝ in z.im..w.im, H' z) := by
      rw [intervalIntegral.integral_const, intervalIntegral.integral_const,
        Complex.real_smul, Complex.real_smul]
      have hsub : w - z = ((w.re - z.re : ℝ) : ℂ) + I * ((w.im - z.im : ℝ) : ℂ) := by
        apply Complex.ext <;> simp
      rw [hsub]
      ring
    have hrem : A w - A z - (w - z) * H' z =
        (∫ x : ℝ in z.re..w.re, (H' (x + z.im * I) - H' z)) +
        I * (∫ y : ℝ in z.im..w.im, (H' (w.re + y * I) - H' z)) := by
      rw [hAdiff, hlin,
        intervalIntegral.integral_sub (hint_x z.re w.re z.im hz.1 hz.2 hwU.1 hwU.2)
          intervalIntegrable_const,
        intervalIntegral.integral_sub (hint_y w.re z.im w.im hwU.1 hwU.2)
          intervalIntegrable_const]
      ring
    rw [smul_eq_mul, hrem]
    have hbound_x : ‖∫ x : ℝ in z.re..w.re, (H' (x + z.im * I) - H' z)‖ ≤
        (c / 2) * |w.re - z.re| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc] at hx
      have hxz : dist ((x : ℂ) + (z.im : ℂ) * I) z < δ₁ := by
        rw [dist_eq_norm]
        have hdiff : ((x : ℂ) + (z.im : ℂ) * I) - z = ((x - z.re : ℝ) : ℂ) := by
          apply Complex.ext <;> simp
        rw [hdiff, Complex.norm_real, Real.norm_eq_abs]
        have hle : |x - z.re| ≤ |w.re - z.re| := by
          rw [abs_le]
          constructor
          · have : min z.re w.re ≤ x := hx.1.le
            have : z.re - |w.re - z.re| ≤ min z.re w.re := by
              rw [le_min_iff]; constructor <;> linarith [neg_abs_le (w.re - z.re), le_abs_self (w.re - z.re)]
            linarith
          · have : x ≤ max z.re w.re := hx.2
            have : max z.re w.re ≤ z.re + |w.re - z.re| := by
              rw [max_le_iff]; constructor <;> linarith [neg_abs_le (w.re - z.re), le_abs_self (w.re - z.re)]
            linarith
        have hδ_lt : δ ≤ δ₁ / 2 := min_le_left _ _
        linarith
      rw [← dist_eq_norm]
      exact (hball hxz).le
    have hbound_y : ‖∫ y : ℝ in z.im..w.im, (H' (w.re + y * I) - H' z)‖ ≤
        (c / 2) * |w.im - z.im| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun y hy => ?_
      rw [Set.uIoc] at hy
      have hyz : dist ((w.re : ℂ) + (y : ℂ) * I) z < δ₁ := by
        rw [dist_eq_norm]
        have hdiff : ((w.re : ℂ) + (y : ℂ) * I) - z =
            ((w.re - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I := by
          apply Complex.ext <;> simp
        rw [hdiff]
        have hyle : |y - z.im| ≤ |w.im - z.im| := by
          rw [abs_le]
          constructor
          · have : min z.im w.im ≤ y := hy.1.le
            have : z.im - |w.im - z.im| ≤ min z.im w.im := by
              rw [le_min_iff]; constructor <;> linarith [neg_abs_le (w.im - z.im), le_abs_self (w.im - z.im)]
            linarith
          · have : y ≤ max z.im w.im := hy.2
            have : max z.im w.im ≤ z.im + |w.im - z.im| := by
              rw [max_le_iff]; constructor <;> linarith [neg_abs_le (w.im - z.im), le_abs_self (w.im - z.im)]
            linarith
        have him_lt : |w.im - z.im| < δ := by
          calc |w.im - z.im| = |(w - z).im| := by simp
            _ ≤ ‖w - z‖ := Complex.abs_im_le_norm _
            _ < δ := hw_dist
        have hδ_lt : δ ≤ δ₁ / 2 := min_le_left _ _
        calc ‖((w.re - z.re : ℝ) : ℂ) + ((y - z.im : ℝ) : ℂ) * I‖
            ≤ ‖((w.re - z.re : ℝ) : ℂ)‖ + ‖((y - z.im : ℝ) : ℂ) * I‖ := norm_add_le _ _
          _ = |w.re - z.re| + |y - z.im| := by
              rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Complex.norm_real,
                Real.norm_eq_abs, Real.norm_eq_abs]
          _ < δ + δ := by linarith
          _ ≤ δ₁ := by linarith
      rw [← dist_eq_norm]
      exact (hball hyz).le
    have hre_le : |w.re - z.re| ≤ ‖w - z‖ := by
      simpa using Complex.abs_re_le_norm (w - z)
    have him_le : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa using Complex.abs_im_le_norm (w - z)
    calc ‖(∫ x : ℝ in z.re..w.re, (H' (x + z.im * I) - H' z)) +
            I * (∫ y : ℝ in z.im..w.im, (H' (w.re + y * I) - H' z))‖
        ≤ ‖∫ x : ℝ in z.re..w.re, (H' (x + z.im * I) - H' z)‖ +
          ‖I * (∫ y : ℝ in z.im..w.im, (H' (w.re + y * I) - H' z))‖ := norm_add_le _ _
      _ = ‖∫ x : ℝ in z.re..w.re, (H' (x + z.im * I) - H' z)‖ +
          ‖∫ y : ℝ in z.im..w.im, (H' (w.re + y * I) - H' z)‖ := by rw [norm_mul, Complex.norm_I, one_mul]
      _ ≤ (c / 2) * |w.re - z.re| + (c / 2) * |w.im - z.im| := add_le_add hbound_x hbound_y
      _ ≤ (c / 2) * ‖w - z‖ + (c / 2) * ‖w - z‖ := by gcongr
      _ = c * ‖w - z‖ := by ring
  have hA_diff : DifferentiableOn ℂ A U :=
    fun z hz => (hA_deriv z hz).differentiableAt.differentiableWithinAt
  have hA_ana : AnalyticOnNhd ℂ A U :=
    (Complex.analyticOnNhd_iff_differentiableOn hU_open).mpr hA_diff
  have hH'_ana : AnalyticOnNhd ℂ H' U :=
    (hA_ana.deriv).congr hU_open (fun z hz => (hA_deriv z hz).deriv)
  have hU_convex : Convex ℝ U := by
    have h1 : Convex ℝ {z : ℂ | -β < z.re} := by
      intro x hx y hy a b ha hb hab
      change -β < (a • x + b • y).re
      have hx' : -β < x.re := hx
      have hy' : -β < y.re := hy
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      rcases eq_or_lt_of_le ha with rfl | ha' <;> nlinarith
    have h2 : Convex ℝ {z : ℂ | z.re < β} := by
      intro x hx y hy a b ha hb hab
      change (a • x + b • y).re < β
      have hx' : x.re < β := hx
      have hy' : y.re < β := hy
      simp only [Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im]
      rcases eq_or_lt_of_le ha with rfl | ha' <;> nlinarith
    exact h1.inter h2
  have hz0_mem : (-(β / 2) : ℂ) ∈ U := by
    simp only [U, Set.mem_ofPred_eq, neg_re, div_ofNat_re, ofReal_re]
    constructor <;> linarith
  have hH'_ev : H' =ᶠ[𝓝 (-(β / 2) : ℂ)] 0 := by
    have hopen : {u : ℂ | u.re < 0} ∈ 𝓝 (-(β / 2) : ℂ) :=
      (isOpen_lt Complex.continuous_re continuous_const).mem_nhds (by simp; linarith)
    filter_upwards [hopen] with u hu
    exact hH'_nonpos u hu.le
  have hH'_zero : Set.EqOn H' 0 U :=
    hH'_ana.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU_convex.isPreconnected hz0_mem hH'_ev
  -- Extend from `{0 ≤ z.re < β}` to `{0 ≤ z.re ≤ β}` by continuity
  intro z hz1 hz2
  by_cases hlt : z.re < β
  · have h := hH'_zero (show z ∈ U from ⟨by linarith, hlt⟩)
    simpa [H', hz1] using h
  · have hre : z.re = β := le_antisymm hz2 (not_lt.mp hlt)
    have hlim : Tendsto (fun n : ℕ => ((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I)
        atTop (𝓝[ {u : ℂ | 0 ≤ u.re ∧ u.re ≤ β} ] z) := by
      rw [tendsto_nhdsWithin_iff]
      refine ⟨?_, Eventually.of_forall fun n => ?_⟩
      · have hseq : Tendsto (fun n : ℕ => β - β / ((n : ℝ) + 2)) atTop (𝓝 β) := by
          have h0 : Tendsto (fun n : ℕ => β / ((n : ℝ) + 2)) atTop (𝓝 0) :=
            tendsto_const_nhds.div_atTop
              (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds)
          simpa using tendsto_const_nhds.sub h0
        have hcomp : Tendsto
            (fun n : ℕ => ((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I)
            atTop (𝓝 ((β : ℂ) + (z.im : ℂ) * I)) :=
          (Complex.continuous_ofReal.tendsto β |>.comp hseq).add tendsto_const_nhds
        have hz_eq : (β : ℂ) + (z.im : ℂ) * I = z := by
          apply Complex.ext <;> simp [hre]
        rwa [hz_eq] at hcomp
      · have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
        have hle1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
        have hdiv_le : β / ((n : ℝ) + 2) ≤ β := div_le_self hβ.le hle1
        have hdiv_pos : 0 < β / ((n : ℝ) + 2) := div_pos hβ hpos
        simp only [Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im,
          mul_one, sub_self, add_zero]
        exact ⟨by linarith, by linarith⟩
    have hH_tendsto : Tendsto
        (fun n : ℕ => H (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I))
        atTop (𝓝 (H z)) :=
      (hcont z ⟨hz1, hz2⟩).tendsto.comp hlim
    have hH_const : ∀ n : ℕ, H (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I) = 0 := by
      intro n
      have hpos : (0 : ℝ) < (n : ℝ) + 2 := by positivity
      have hle1 : (1 : ℝ) ≤ (n : ℝ) + 2 := by linarith [Nat.cast_nonneg (α := ℝ) n]
      have hdiv_le : β / ((n : ℝ) + 2) ≤ β := div_le_self hβ.le hle1
      have hdiv_pos : 0 < β / ((n : ℝ) + 2) := div_pos hβ hpos
      have huU : (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I) ∈ U := by
        simp only [U, Set.mem_ofPred_eq, add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im,
          I_im, mul_one, sub_self, add_zero]
        exact ⟨by linarith, by linarith⟩
      have h := hH'_zero huU
      have h0 : 0 ≤ ((((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I)).re := by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
          Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
        linarith
      change H' (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I) = 0 at h
      rwa [show H' (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I) =
        H (((β - β / ((n : ℝ) + 2) : ℝ) : ℂ) + (z.im : ℂ) * I) from if_pos h0] at h
    simp_rw [hH_const] at hH_tendsto
    exact tendsto_nhds_unique hH_tendsto tendsto_const_nhds

private lemma eq_zero_on_uIcc_strip_of_eq_zero_on_imag_axis
    {H : ℂ → ℂ} {β : ℝ} (hβ : β ≠ 0)
    (hcont : ContinuousOn H {z : ℂ | min 0 β ≤ z.re ∧ z.re ≤ max 0 β})
    (hdiff : DifferentiableOn ℂ H {z : ℂ | min 0 β < z.re ∧ z.re < max 0 β})
    (hzero : ∀ y : ℝ, H (y * I) = 0) :
    ∀ z : ℂ, min 0 β ≤ z.re → z.re ≤ max 0 β → H z = 0 := by
  rcases lt_or_gt_of_ne hβ with hneg | hpos
  · have hmin : min 0 β = β := min_eq_right hneg.le
    have hmax : max 0 β = 0 := max_eq_left hneg.le
    rw [hmin, hmax] at hcont hdiff ⊢
    have hneg_pos : 0 < -β := neg_pos.mpr hneg
    have hcont' : ContinuousOn (fun w : ℂ => H (-w)) {w : ℂ | 0 ≤ w.re ∧ w.re ≤ -β} := by
      refine hcont.comp continuousOn_neg fun w hw => ?_
      simp only [Set.mem_ofPred_eq, neg_re] at hw ⊢
      exact ⟨by linarith, by linarith⟩
    have hdiff' : DifferentiableOn ℂ (fun w : ℂ => H (-w)) {w : ℂ | 0 < w.re ∧ w.re < -β} := by
      refine hdiff.comp (differentiableOn_neg _) fun w hw => ?_
      simp only [Set.mem_ofPred_eq, neg_re] at hw ⊢
      exact ⟨by linarith, by linarith⟩
    have hzero' : ∀ y : ℝ, H (-(y * I)) = 0 := by
      intro y
      have : -(y * I) = ((-y : ℝ) : ℂ) * I := by push_cast; ring
      rw [this, hzero]
    intro z hz1 hz2
    have h := eq_zero_on_closed_strip_of_eq_zero_on_imag_axis hneg_pos hcont' hdiff' hzero'
      (-z) (by simp; linarith) (by simp; linarith)
    simpa using h
  · have hmin : min 0 β = 0 := min_eq_left hpos.le
    have hmax : max 0 β = β := max_eq_right hpos.le
    rw [hmin, hmax] at hcont hdiff ⊢
    exact eq_zero_on_closed_strip_of_eq_zero_on_imag_axis hpos hcont hdiff hzero

/-! ### Measure-theoretic Esscher marginal lemmas -/

private lemma measurable_X_F
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (t : NNReal) :
    Measurable[F t] (X t) := by
  rw [measurable_iff_comap_le, hNatural t]
  refine le_trans ?_ le_sup_left
  exact le_iSup₂_of_le t (le_refl t) le_rfl

private lemma measurable_X
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F) (t : NNReal) :
    Measurable (X t) :=
  (measurable_X_F P F X hNatural t).mono (F.le t) le_rfl

end EsscherTripletWitnessProp2Aux


namespace EsscherTimeConsistencyAux

open MeasureTheory ProbabilityTheory Set Filter EsscherTripletWitnessProp2Aux
open scoped NNReal ENNReal Real

/-! ### Part 1: Additive convolution and explicit compound Poisson measures -/

private noncomputable def addConv (μ ν : Measure ℝ) : Measure ℝ :=
  (μ.prod ν).map (fun p : ℝ × ℝ => p.1 + p.2)

private lemma lintegral_addConv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν]
    {f : ℝ → ℝ≥0∞} (hf : Measurable f) :
    ∫⁻ z, f z ∂(addConv μ ν) = ∫⁻ x, ∫⁻ y, f (x + y) ∂ν ∂μ := by
  dsimp only [addConv]
  rw [lintegral_map hf measurable_add]
  exact lintegral_prod (fun p : ℝ × ℝ => f (p.1 + p.2)) (hf.comp measurable_add).aemeasurable

private lemma addConv_univ (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] :
    addConv μ ν Set.univ = μ Set.univ * ν Set.univ := by
  dsimp only [addConv]
  rw [Measure.map_apply measurable_add MeasurableSet.univ, Set.preimage_univ,
    ← Set.univ_prod_univ, Measure.prod_prod]

private instance isFiniteMeasure_addConv (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] : IsFiniteMeasure (addConv μ ν) := by
  refine ⟨?_⟩
  rw [addConv_univ]
  exact ENNReal.mul_lt_top (measure_lt_top μ Set.univ) (measure_lt_top ν Set.univ)

private instance isProbabilityMeasure_addConv (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] : IsProbabilityMeasure (addConv μ ν) := by
  refine ⟨?_⟩
  rw [addConv_univ, measure_univ, measure_univ, mul_one]

private lemma charFun_addConv (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν] (ξ : ℝ) :
    charFun (addConv μ ν) ξ = charFun μ ξ * charFun ν ξ := by
  rw [charFun_apply_real, charFun_apply_real, charFun_apply_real]
  dsimp only [addConv]
  have hmeas : Measurable (fun z : ℝ => Complex.exp ((ξ : ℂ) * (z : ℂ) * Complex.I)) := by
    fun_prop
  rw [integral_map measurable_add.aemeasurable hmeas.aestronglyMeasurable]
  have hint_prod : Integrable (fun p : ℝ × ℝ =>
      Complex.exp ((ξ : ℂ) * ((p.1 + p.2 : ℝ) : ℂ) * Complex.I)) (μ.prod ν) := by
    refine Integrable.of_bound (hmeas.comp measurable_add).aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
    have hnorm : ‖Complex.exp ((ξ : ℂ) * ((p.1 + p.2 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      have : (ξ : ℂ) * ((p.1 + p.2 : ℝ) : ℂ) * Complex.I = (((ξ * (p.1 + p.2) : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    exact hnorm.le
  rw [integral_prod _ hint_prod]
  have hsplit : ∀ x y : ℝ,
      Complex.exp ((ξ : ℂ) * ((x + y : ℝ) : ℂ) * Complex.I) =
      Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) * Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) := by
    intro x y
    rw [← Complex.exp_add]
    congr 1; push_cast; ring
  simp_rw [hsplit, integral_const_mul, integral_mul_const]

private lemma lintegral_exp_addConv (μ ν : Measure ℝ) [SFinite μ] [SFinite ν] (β : ℝ) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (β * z)) ∂(addConv μ ν)) =
    (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂μ) *
      (∫⁻ y, ENNReal.ofReal (Real.exp (β * y)) ∂ν) := by
  have hm : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (β * z))) := by fun_prop
  rw [lintegral_addConv μ ν hm]
  have hfac : ∀ x y : ℝ,
      ENNReal.ofReal (Real.exp (β * (x + y))) =
      ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (Real.exp (β * y)) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2; ring
  simp_rw [hfac, lintegral_const_mul _ hm, lintegral_mul_const _ hm]

private noncomputable def iterConv (ρ : Measure ℝ) : ℕ → Measure ℝ
  | 0 => Measure.dirac 0
  | k + 1 => addConv (iterConv ρ k) ρ

private lemma isFiniteMeasure_iterConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    ∀ k : ℕ, IsFiniteMeasure (iterConv ρ k)
  | 0 => by dsimp only [iterConv]; infer_instance
  | k + 1 => by
    have := isFiniteMeasure_iterConv ρ k
    dsimp only [iterConv]; infer_instance

private lemma iterConv_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    ∀ k : ℕ, iterConv ρ k Set.univ = (ρ Set.univ) ^ k
  | 0 => by simp [iterConv]
  | k + 1 => by
    have := isFiniteMeasure_iterConv ρ k
    simp [iterConv, addConv_univ, iterConv_univ ρ k, pow_succ]

private lemma charFun_iterConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] (ξ : ℝ) :
    ∀ k : ℕ, charFun (iterConv ρ k) ξ = (charFun ρ ξ) ^ k
  | 0 => by
    rw [pow_zero]
    simp [iterConv]
  | k + 1 => by
    have := isFiniteMeasure_iterConv ρ k
    dsimp only [iterConv]
    rw [charFun_addConv, charFun_iterConv ρ ξ k, pow_succ]

private lemma lintegral_exp_iterConv (ρ : Measure ℝ) [IsFiniteMeasure ρ] (β : ℝ) :
    ∀ k : ℕ,
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * z)) ∂(iterConv ρ k)) =
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂ρ) ^ k
  | 0 => by
    simp [iterConv]
  | k + 1 => by
    have := isFiniteMeasure_iterConv ρ k
    dsimp only [iterConv]
    rw [lintegral_exp_addConv, lintegral_exp_iterConv ρ β k, pow_succ]

private noncomputable def compoundPoisson (ρ : Measure ℝ) : Measure ℝ :=
  Measure.sum (fun k : ℕ =>
    ENNReal.ofReal (Real.exp (-(ρ Set.univ).toReal) / (Nat.factorial k : ℝ)) • iterConv ρ k)

private lemma compoundPoisson_univ (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    compoundPoisson ρ Set.univ = 1 := by
  dsimp only [compoundPoisson]
  rw [Measure.sum_apply _ MeasurableSet.univ]
  set lam : ℝ := (ρ Set.univ).toReal
  have hlam_nonneg : 0 ≤ lam := ENNReal.toReal_nonneg
  have hterm : ∀ k : ℕ,
      (ENNReal.ofReal (Real.exp (-lam) / (Nat.factorial k : ℝ)) • iterConv ρ k) Set.univ =
      ENNReal.ofReal (Real.exp (-lam) * (lam ^ k / (Nat.factorial k : ℝ))) := by
    intro k
    rw [Measure.smul_apply, smul_eq_mul, iterConv_univ ρ k]
    have hρ : ρ Set.univ = ENNReal.ofReal lam := (ENNReal.ofReal_toReal (measure_ne_top ρ Set.univ)).symm
    rw [hρ, ← ENNReal.ofReal_pow hlam_nonneg, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  simp_rw [hterm]
  have hsumm : Summable (fun k : ℕ => Real.exp (-lam) * (lam ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial lam).mul_left _
  have htsum : (∑' k : ℕ, lam ^ k / (Nat.factorial k : ℝ)) = Real.exp lam := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm,
    tsum_mul_left, htsum, ← Real.exp_add, neg_add_cancel, Real.exp_zero, ENNReal.ofReal_one]

private instance isProbabilityMeasure_compoundPoisson (ρ : Measure ℝ) [IsFiniteMeasure ρ] :
    IsProbabilityMeasure (compoundPoisson ρ) :=
  ⟨compoundPoisson_univ ρ⟩

private lemma charFun_compoundPoisson (ρ : Measure ℝ) [IsFiniteMeasure ρ] (ξ : ℝ) :
    charFun (compoundPoisson ρ) ξ =
      Complex.exp (charFun ρ ξ - ((ρ Set.univ).toReal : ℂ)) := by
  rw [charFun_apply_real]
  dsimp only [compoundPoisson]
  set lam : ℝ := (ρ Set.univ).toReal
  have hlam_nonneg : 0 ≤ lam := ENNReal.toReal_nonneg
  let f : ℝ → ℂ := fun x => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I)
  have hf_meas : Measurable f := by dsimp only [f]; fun_prop
  have hf_norm : ∀ x : ℝ, ‖f x‖ = 1 := fun x => by
    dsimp only [f]
    have : (ξ : ℂ) * (x : ℂ) * Complex.I = (((ξ * x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
    rw [this, Complex.norm_exp_ofReal_mul_I]
  have hf_int : Integrable f (Measure.sum fun k : ℕ =>
      ENNReal.ofReal (Real.exp (-lam) / (Nat.factorial k : ℝ)) • iterConv ρ k) := by
    have : IsProbabilityMeasure (Measure.sum fun k : ℕ =>
        ENNReal.ofReal (Real.exp (-lam) / (Nat.factorial k : ℝ)) • iterConv ρ k) :=
      isProbabilityMeasure_compoundPoisson ρ
    exact Integrable.of_bound hf_meas.aestronglyMeasurable 1 (ae_of_all _ fun x => (hf_norm x).le)
  rw [integral_sum_measure hf_int]
  have hterm : ∀ k : ℕ,
      (∫ x, f x ∂(ENNReal.ofReal (Real.exp (-lam) / (Nat.factorial k : ℝ)) • iterConv ρ k)) =
      (Real.exp (-lam) : ℂ) * ((charFun ρ ξ) ^ k / (Nat.factorial k : ℂ)) := by
    intro k
    have := isFiniteMeasure_iterConv ρ k
    rw [integral_smul_measure, ENNReal.toReal_ofReal (by positivity), Complex.real_smul]
    have hcf : (∫ x, f x ∂(iterConv ρ k)) = (charFun ρ ξ) ^ k := by
      rw [← charFun_apply_real, charFun_iterConv ρ ξ k]
    rw [hcf]
    push_cast
    ring
  simp_rw [hterm, tsum_mul_left]
  have htsum : (∑' k : ℕ, (charFun ρ ξ) ^ k / (Nat.factorial k : ℂ)) = Complex.exp (charFun ρ ξ) := by
    rw [Complex.exp_eq_exp_ℂ, NormedSpace.exp_eq_tsum_div]
  rw [htsum, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma lintegral_exp_compoundPoisson (ρ : Measure ℝ) [IsFiniteMeasure ρ] (β : ℝ)
    (hfin : ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂ρ ≠ ⊤) :
    (∫⁻ z, ENNReal.ofReal (Real.exp (β * z)) ∂(compoundPoisson ρ)) =
    ENNReal.ofReal (Real.exp
      ((∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂ρ).toReal - (ρ Set.univ).toReal)) := by
  dsimp only [compoundPoisson]
  rw [lintegral_sum_measure]
  set lam : ℝ := (ρ Set.univ).toReal
  set M : ℝ := (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂ρ).toReal
  have hM_nonneg : 0 ≤ M := ENNReal.toReal_nonneg
  have hterm : ∀ k : ℕ,
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * z)) ∂
        (ENNReal.ofReal (Real.exp (-lam) / (Nat.factorial k : ℝ)) • iterConv ρ k)) =
      ENNReal.ofReal (Real.exp (-lam) * (M ^ k / (Nat.factorial k : ℝ))) := by
    intro k
    rw [lintegral_smul_measure, smul_eq_mul, lintegral_exp_iterConv ρ β k]
    have hM_eq : (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂ρ) = ENNReal.ofReal M :=
      (ENNReal.ofReal_toReal hfin).symm
    rw [hM_eq, ← ENNReal.ofReal_pow hM_nonneg, ← ENNReal.ofReal_mul (by positivity)]
    congr 1; ring
  simp_rw [hterm]
  have hsumm : Summable (fun k : ℕ => Real.exp (-lam) * (M ^ k / (Nat.factorial k : ℝ))) :=
    (Real.summable_pow_div_factorial M).mul_left _
  have htsum : (∑' k : ℕ, M ^ k / (Nat.factorial k : ℝ)) = Real.exp M := by
    rw [Real.exp_eq_exp_ℝ, NormedSpace.exp_eq_tsum_div]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) hsumm,
    tsum_mul_left, htsum, ← Real.exp_add]
  congr 2; ring

/-! ### Part 2: Fixed N(0, 1) Gaussian smoothing kernel -/

private noncomputable def gaussianSmoothDensity (ν : Measure ℝ) (x : ℝ) : ℝ :=
  ∫ y, gaussianPDFReal 0 1 (x - y) ∂ν

private lemma gaussianPDFReal_std_eq_fourier (u : ℝ) :
    gaussianPDFReal 0 1 u =
      (√(2 * Real.pi))⁻¹ *
        (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ) * Complex.I)).re := by
  have hcf := charFun_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0)) (-u)
  rw [charFun_apply_real, integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)] at hcf
  have hsimp :
      (∫ ξ : ℝ, gaussianPDFReal 0 1 ξ • Complex.exp (((-u : ℝ) : ℂ) * (ξ : ℂ) * Complex.I)) =
      (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (u : ℂ) * Complex.I)) := by
    refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
    dsimp only
    rw [Complex.real_smul]
    congr 2
    push_cast; ring
  rw [hsimp] at hcf
  have hre := congrArg Complex.re hcf
  have hre_rhs :
      (Complex.exp (((-u : ℝ) : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((1 : ℝ≥0) : ℂ) * ((-u : ℝ) : ℂ) ^ 2 / 2)).re =
      Real.exp (-(u ^ 2) / 2) := by
    have : ((-u : ℝ) : ℂ) * ((0 : ℝ) : ℂ) * Complex.I - ((1 : ℝ≥0) : ℂ) * ((-u : ℝ) : ℂ) ^ 2 / 2 =
        (((-(u ^ 2) / 2 : ℝ) : ℂ)) := by
      push_cast; ring
    rw [this, ← Complex.ofReal_exp, Complex.ofReal_re]
  rw [hre_rhs] at hre
  rw [hre, gaussianPDFReal]
  simp only [NNReal.coe_one, mul_one, sub_zero]

private lemma gaussianSmoothDensity_eq_fourier (ν : Measure ℝ) [IsProbabilityMeasure ν] (x : ℝ) :
    gaussianSmoothDensity ν x =
      (√(2 * Real.pi))⁻¹ *
        (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I) *
          charFun ν ξ).re := by
  dsimp only [gaussianSmoothDensity]
  have hstep : (∫ y, gaussianPDFReal 0 1 (x - y) ∂ν) =
      ∫ y, (√(2 * Real.pi))⁻¹ *
        (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * ((x - y : ℝ) : ℂ) * Complex.I)).re ∂ν :=
    integral_congr_ae (ae_of_all _ fun y => gaussianPDFReal_std_eq_fourier (x - y))
  rw [hstep, integral_const_mul]
  congr 1
  have hF_int : Integrable (fun p : ℝ × ℝ =>
      (gaussianPDFReal 0 1 p.2 : ℂ) * Complex.exp (-(p.2 : ℂ) * ((x - p.1 : ℝ) : ℂ) * Complex.I))
      (ν.prod volume) := by
    have hmeas : Measurable (fun p : ℝ × ℝ =>
        (gaussianPDFReal 0 1 p.2 : ℂ) * Complex.exp (-(p.2 : ℂ) * ((x - p.1 : ℝ) : ℂ) * Complex.I)) := by
      have hm1 : Measurable (fun p : ℝ × ℝ => gaussianPDFReal 0 1 p.2) :=
        (measurable_gaussianPDFReal 0 1).comp measurable_snd
      fun_prop
    have hdom : Integrable (fun p : ℝ × ℝ => gaussianPDFReal 0 1 p.2) (ν.prod volume) :=
      (integrable_gaussianPDFReal 0 1).comp_snd ν
    refine Integrable.mono' hdom hmeas.aestronglyMeasurable (ae_of_all _ fun p => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 p.2)]
    have h1 : ‖Complex.exp (-(p.2 : ℂ) * ((x - p.1 : ℝ) : ℂ) * Complex.I)‖ = 1 := by
      have : -(p.2 : ℂ) * ((x - p.1 : ℝ) : ℂ) * Complex.I = (((-(p.2 * (x - p.1)) : ℝ) : ℂ) * Complex.I) := by
        push_cast; ring
      rw [this, Complex.norm_exp_ofReal_mul_I]
    rw [h1, mul_one]
  have hre_pull :
      (∫ y, (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) *
          Complex.exp (-(ξ : ℂ) * ((x - y : ℝ) : ℂ) * Complex.I)).re ∂ν) =
      (∫ y, (∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) *
          Complex.exp (-(ξ : ℂ) * ((x - y : ℝ) : ℂ) * Complex.I)) ∂ν).re := by
    have hint_outer : Integrable (fun y =>
        ∫ ξ : ℝ, (gaussianPDFReal 0 1 ξ : ℂ) *
          Complex.exp (-(ξ : ℂ) * ((x - y : ℝ) : ℂ) * Complex.I)) ν :=
      hF_int.integral_prod_left
    exact Complex.reCLM.integral_comp_comm hint_outer
  rw [hre_pull]
  congr 1
  rw [integral_integral_swap hF_int]
  refine integral_congr_ae (ae_of_all _ fun ξ => ?_)
  have hsplit : ∀ y : ℝ,
      (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * ((x - y : ℝ) : ℂ) * Complex.I) =
      ((gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I)) *
        Complex.exp ((ξ : ℂ) * (y : ℂ) * Complex.I) := by
    intro y
    symm
    rw [mul_assoc, ← Complex.exp_add]
    congr 2; push_cast; ring
  simp_rw [hsplit, integral_const_mul, ← charFun_apply_real]

private lemma lintegral_exp_mul_gaussianSmoothDensity
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (β : ℝ) :
    (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) *
      ENNReal.ofReal (gaussianSmoothDensity ν x) ∂volume) =
    (∫⁻ y, ENNReal.ofReal (Real.exp (β * y)) ∂ν) * ENNReal.ofReal (Real.exp (β ^ 2 / 2)) := by
  have hdens_lint : ∀ x : ℝ,
      ENNReal.ofReal (gaussianSmoothDensity ν x) =
      ∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 (x - y)) ∂ν := by
    intro x
    dsimp only [gaussianSmoothDensity]
    have hmeas : Measurable (fun y : ℝ => gaussianPDFReal 0 1 (x - y)) :=
      (measurable_gaussianPDFReal 0 1).comp (measurable_const.sub measurable_id)
    have hbd : ∀ y : ℝ, ‖gaussianPDFReal 0 1 (x - y)‖ ≤ (√(2 * Real.pi))⁻¹ := fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gaussianPDFReal_nonneg 0 1 _), gaussianPDFReal]
      simp only [NNReal.coe_one, mul_one, sub_zero]
      have hle : Real.exp (-(x - y) ^ 2 / 2) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg (x - y)])
      calc (√(2 * Real.pi))⁻¹ * Real.exp (-(x - y) ^ 2 / 2)
          ≤ (√(2 * Real.pi))⁻¹ * 1 := mul_le_mul_of_nonneg_left hle (by positivity)
        _ = (√(2 * Real.pi))⁻¹ := mul_one _
    have hint : Integrable (fun y : ℝ => gaussianPDFReal 0 1 (x - y)) ν :=
      Integrable.of_bound hmeas.aestronglyMeasurable _ (ae_of_all _ hbd)
    exact ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => gaussianPDFReal_nonneg 0 1 _)
  simp_rw [hdens_lint]
  have hpull : ∀ x : ℝ,
      ENNReal.ofReal (Real.exp (β * x)) * (∫⁻ y, ENNReal.ofReal (gaussianPDFReal 0 1 (x - y)) ∂ν) =
      ∫⁻ y, ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianPDFReal 0 1 (x - y)) ∂ν := by
    intro x
    have hm : Measurable (fun y : ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 (x - y))) :=
      ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 1).comp (measurable_const.sub measurable_id))
    exact (lintegral_const_mul _ hm).symm
  simp_rw [hpull]
  have hprod_meas : AEMeasurable (fun p : ℝ × ℝ =>
      ENNReal.ofReal (Real.exp (β * p.1)) * ENNReal.ofReal (gaussianPDFReal 0 1 (p.1 - p.2)))
      (volume.prod ν) := by
    have hm1 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (Real.exp (β * p.1))) := by fun_prop
    have hm2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal (gaussianPDFReal 0 1 (p.1 - p.2))) :=
      ENNReal.measurable_ofReal.comp ((measurable_gaussianPDFReal 0 1).comp measurable_sub)
    exact (hm1.mul hm2).aemeasurable
  rw [lintegral_lintegral_swap hprod_meas]
  have hmgf_std :
      (∫⁻ u : ℝ, ENNReal.ofReal (Real.exp (β * u)) * ENNReal.ofReal (gaussianPDFReal 0 1 u) ∂volume) =
      ENNReal.ofReal (Real.exp (β ^ 2 / 2)) := by
    have hmgf := congrFun (mgf_id_gaussianReal (μ := (0 : ℝ)) (v := (1 : ℝ≥0))) β
    simp only [mgf, id_eq, zero_mul, zero_add, NNReal.coe_one, one_mul] at hmgf
    rw [integral_gaussianReal_eq_integral_smul (one_ne_zero : (1 : ℝ≥0) ≠ 0)] at hmgf
    simp only [smul_eq_mul] at hmgf
    have hhint : Integrable (fun u : ℝ => gaussianPDFReal 0 1 u * Real.exp (β * u)) volume := by
      by_contra hnot
      have h0 := integral_undef hnot
      rw [hmgf] at h0
      exact (Real.exp_pos (β ^ 2 / 2)).ne' h0
    have hcongr : ∀ u : ℝ,
        ENNReal.ofReal (Real.exp (β * u)) * ENNReal.ofReal (gaussianPDFReal 0 1 u) =
        ENNReal.ofReal (gaussianPDFReal 0 1 u * Real.exp (β * u)) := by
      intro u
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), mul_comm]
    simp_rw [hcongr]
    rw [← ofReal_integral_eq_lintegral_ofReal hhint
      (ae_of_all _ fun u => mul_nonneg (gaussianPDFReal_nonneg 0 1 u) (Real.exp_nonneg _)), hmgf]
  have hinner : ∀ y : ℝ,
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianPDFReal 0 1 (x - y)) ∂volume) =
      ENNReal.ofReal (Real.exp (β * y)) * ENNReal.ofReal (Real.exp (β ^ 2 / 2)) := by
    intro y
    rw [← lintegral_add_right_eq_self (fun x =>
      ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianPDFReal 0 1 (x - y))) y]
    have hshift : ∀ u : ℝ,
        ENNReal.ofReal (Real.exp (β * (u + y))) * ENNReal.ofReal (gaussianPDFReal 0 1 (u + y - y)) =
        ENNReal.ofReal (Real.exp (β * y)) *
          (ENNReal.ofReal (Real.exp (β * u)) * ENNReal.ofReal (gaussianPDFReal 0 1 u)) := by
      intro u
      rw [add_sub_cancel_right]
      have hexp : Real.exp (β * (u + y)) = Real.exp (β * y) * Real.exp (β * u) := by
        rw [← Real.exp_add]; congr 1; ring
      rw [hexp, ENNReal.ofReal_mul (Real.exp_nonneg _), mul_assoc]
    simp_rw [hshift]
    have hm_u : Measurable (fun u : ℝ =>
        ENNReal.ofReal (Real.exp (β * u)) * ENNReal.ofReal (gaussianPDFReal 0 1 u)) :=
      (by fun_prop : Measurable (fun u : ℝ => ENNReal.ofReal (Real.exp (β * u)))).mul
        (ENNReal.measurable_ofReal.comp (measurable_gaussianPDFReal 0 1))
    rw [lintegral_const_mul _ hm_u, hmgf_std]
  simp_rw [hinner]
  rw [lintegral_mul_const _ (by fun_prop : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (β * y))))]

/-! ### Part 3: Exponential integrability from Lévy–Khintchine + large-jump condition -/

private lemma exp_integrable_of_charFun_levyKhintchine
    (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (T : ProbabilityTheory.LevyKhintchineTriple) (t : NNReal) (β : ℝ)
    (hCF : ∀ ξ : ℝ, charFun μ ξ =
      Complex.exp (((t : ℝ) : ℂ) * Kyprianou.Ch01.levyTripleExponent T ξ))
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (β * x)) {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    Integrable (fun x : ℝ => Real.exp (β * x)) μ := by
  let A : ℕ → Set ℝ := fun n => {x : ℝ | (1 : ℝ) / (n + 1 : ℝ) ≤ |x| ∧ |x| ≤ (n + 1 : ℝ)}
  have hA_meas : ∀ n : ℕ, MeasurableSet (A n) := fun n =>
    (measurableSet_le measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hA_finite : ∀ n : ℕ, T.levyMeasure (A n) < ⊤ := by
    intro n
    set c : ℝ := min 1 ((1 : ℝ) / (n + 1 : ℝ)) ^ 2
    have hc_pos : 0 < c := by
      dsimp only [c]
      have h1 : (0 : ℝ) < (1 : ℝ) / (n + 1 : ℝ) := by positivity
      exact sq_pos_of_pos (lt_min zero_lt_one h1)
    have hle : ENNReal.ofReal c * T.levyMeasure (A n) ≤
        ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure := by
      calc ENNReal.ofReal c * T.levyMeasure (A n)
          = ∫⁻ _ in A n, ENNReal.ofReal c ∂T.levyMeasure := by
            rw [setLIntegral_const, mul_comm]
        _ ≤ ∫⁻ x in A n, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure := by
            refine setLIntegral_mono' (hA_meas n) fun x hx => ENNReal.ofReal_le_ofReal ?_
            have hx1 : (1 : ℝ) / (n + 1 : ℝ) ≤ |x| := hx.1
            have hmin : min 1 ((1 : ℝ) / (n + 1 : ℝ)) ≤ min 1 |x| := min_le_min_left 1 hx1
            have hsq : (min 1 ((1 : ℝ) / (n + 1 : ℝ))) ^ 2 ≤ (min 1 |x|) ^ 2 :=
              pow_le_pow_left₀ (le_min zero_le_one (by positivity)) hmin 2
            have hmin_sq : (min 1 |x|) ^ 2 ≤ min 1 (x ^ 2) := by
              by_cases h : |x| ≤ 1
              · rw [min_eq_right h, sq_abs, min_eq_right (by nlinarith [abs_nonneg x, sq_abs x])]
              · push Not at h
                rw [min_eq_left h.le, one_pow, min_eq_left (by nlinarith [sq_abs x])]
            exact hsq.trans hmin_sq
        _ ≤ ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure :=
            setLIntegral_le_lintegral (A n) _
    have hlt_top : ∫⁻ x, ENNReal.ofReal (min 1 (x ^ 2)) ∂T.levyMeasure < ⊤ := by
      have hint := EsscherTripletWitnessProp2Aux.integrable_min_one_sq T
      have hfin := hint.hasFiniteIntegral
      rw [hasFiniteIntegral_iff_enorm] at hfin
      have heq : (fun x : ℝ => ‖min 1 (x ^ 2)‖ₑ) = fun x : ℝ => ENNReal.ofReal (min 1 (x ^ 2)) := by
        ext x; rw [Real.enorm_eq_ofReal (le_min zero_le_one (sq_nonneg x))]
      simpa only [heq] using hfin
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hc_pos).ne'] at hle
    exact (lt_irrefl ⊤) (lt_of_le_of_lt hle hlt_top)
  let ρ : ℕ → Measure ℝ := fun n => ((t : ℝ≥0∞)) • T.levyMeasure.restrict (A n)
  have hρ_fin : ∀ n : ℕ, IsFiniteMeasure (ρ n) := fun n => by
    refine ⟨?_⟩
    dsimp only [ρ]
    rw [Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hA_finite n)
  let m_n : ℕ → ℝ := fun n =>
    (t : ℝ) * (T.drift - ∫ x in A n, (if |x| < 1 then x else 0) ∂T.levyMeasure)
  let v_t : ℝ≥0 := t * T.gaussianVariance
  let μn : ℕ → Measure ℝ := fun n => addConv (gaussianReal (m_n n) v_t) (compoundPoisson (ρ n))
  have hμn_prob : ∀ n : ℕ, IsProbabilityMeasure (μn n) := fun n => by
    dsimp only [μn]; infer_instance
  have hA_exp_int : ∀ (n : ℕ) (γ : ℝ), IntegrableOn (fun x : ℝ => Real.exp (γ * x)) (A n) T.levyMeasure := by
    intro n γ
    have : IsFiniteMeasure (T.levyMeasure.restrict (A n)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hA_finite n⟩
    refine Integrable.of_bound (by fun_prop : Measurable (fun x : ℝ => Real.exp (γ * x))).aestronglyMeasurable
      (Real.exp (|γ| * (n + 1 : ℝ))) ?_
    filter_upwards [ae_restrict_mem (hA_meas n)] with x hx
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    refine Real.exp_le_exp.mpr ?_
    calc γ * x ≤ |γ * x| := le_abs_self _
      _ = |γ| * |x| := abs_mul γ x
      _ ≤ |γ| * (n + 1 : ℝ) := mul_le_mul_of_nonneg_left hx.2 (abs_nonneg _)
  have hA_trunc_int : ∀ n : ℕ, IntegrableOn (fun x : ℝ => if |x| < 1 then x else 0) (A n) T.levyMeasure := by
    intro n
    have : IsFiniteMeasure (T.levyMeasure.restrict (A n)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hA_finite n⟩
    have hm : Measurable (fun x : ℝ => if |x| < 1 then x else 0) :=
      Measurable.ite (measurableSet_lt measurable_abs measurable_const) measurable_id measurable_const
    refine Integrable.of_bound hm.aestronglyMeasurable 1 (ae_of_all _ fun x => ?_)
    split_ifs with h
    · rw [Real.norm_eq_abs]; exact h.le
    · simp
  -- Step 3a: charFun (μn n) ξ → charFun μ ξ
  have hCF_μn : ∀ (n : ℕ) (ξ : ℝ),
      charFun (μn n) ξ = Complex.exp (((t : ℝ) : ℂ) *
        ((T.drift : ℂ) * (Complex.I * (ξ : ℂ)) +
          ((T.gaussianVariance : ℝ) : ℂ) * (Complex.I * (ξ : ℂ)) ^ 2 / 2 +
          ∫ x in A n, EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ)) x ∂T.levyMeasure)) := by
    intro n ξ
    dsimp only [μn]
    rw [charFun_addConv, charFun_gaussianReal, charFun_compoundPoisson, ← Complex.exp_add]
    congr 1
    have hAn_fin : IsFiniteMeasure (T.levyMeasure.restrict (A n)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hA_finite n⟩
    have h1_int : Integrable (fun _ : ℝ => (1 : ℂ)) (T.levyMeasure.restrict (A n)) :=
      integrable_const 1
    have he_int : Integrable (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))
        (T.levyMeasure.restrict (A n)) :=
      Integrable.of_bound
        (by fun_prop : Measurable (fun x : ℝ => Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I))).aestronglyMeasurable
        1 (ae_of_all _ fun x => by
          have : (ξ : ℂ) * (x : ℂ) * Complex.I = (((ξ * x : ℝ) : ℂ) * Complex.I) := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I])
    have hcf_ρ : charFun (ρ n) ξ - (((ρ n Set.univ).toReal) : ℂ) =
        ((t : ℝ) : ℂ) * ∫ x in A n, (Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) - 1) ∂T.levyMeasure := by
      rw [charFun_apply_real, integral_sub he_int h1_int, integral_const,
        Measure.real_def, Measure.restrict_apply_univ, Complex.real_smul, mul_one]
      dsimp only [ρ]
      rw [integral_smul_measure, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
        ENNReal.toReal_mul, ENNReal.coe_toReal, Complex.real_smul]
      push_cast; ring
    have htrunc_c :
        (∫ x in A n, (Complex.I * (ξ : ℂ)) * (x : ℂ) * (if |x| < 1 then (1 : ℂ) else 0) ∂T.levyMeasure) =
        (Complex.I * (ξ : ℂ)) * ((∫ x in A n, (if |x| < 1 then x else 0) ∂T.levyMeasure : ℝ) : ℂ) := by
      have heq : ∀ x : ℝ,
          (Complex.I * (ξ : ℂ)) * (x : ℂ) * (if |x| < 1 then (1 : ℂ) else 0) =
          (Complex.I * (ξ : ℂ)) * Complex.ofRealCLM (if |x| < 1 then x else 0) := fun x => by
        split_ifs <;> simp
      simp_rw [heq, integral_const_mul]
      rw [Complex.ofRealCLM.integral_comp_comm (hA_trunc_int n)]
      rfl
    have hcomp_split :
        (∫ x in A n, EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ)) x ∂T.levyMeasure) =
        (∫ x in A n, (Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) - 1) ∂T.levyMeasure) -
        (Complex.I * (ξ : ℂ)) * ((∫ x in A n, (if |x| < 1 then x else 0) ∂T.levyMeasure : ℝ) : ℂ) := by
      dsimp only [EsscherTripletWitnessProp2Aux.expCompIntegrand]
      have he_sub_int : Integrable (fun x : ℝ => Complex.exp ((Complex.I * (ξ : ℂ)) * (x : ℂ)) - 1)
          (T.levyMeasure.restrict (A n)) := by
        have hce : ∀ x : ℝ, Complex.exp ((Complex.I * (ξ : ℂ)) * (x : ℂ)) =
            Complex.exp ((ξ : ℂ) * (x : ℂ) * Complex.I) := fun x => by congr 1; ring
        simp_rw [hce]
        exact he_int.sub h1_int
      have htr_int : Integrable (fun x : ℝ => (Complex.I * (ξ : ℂ)) * (x : ℂ) * (if |x| < 1 then (1 : ℂ) else 0))
          (T.levyMeasure.restrict (A n)) := by
        have : (fun x : ℝ => (Complex.I * (ξ : ℂ)) * (x : ℂ) * (if |x| < 1 then (1 : ℂ) else 0)) =
            fun x : ℝ => (Complex.I * (ξ : ℂ)) * Complex.ofRealCLM (if |x| < 1 then x else 0) := by
          ext x; split_ifs <;> simp
        rw [this]
        exact (Complex.ofRealCLM.integrable_comp (hA_trunc_int n)).const_mul _
      rw [integral_sub he_sub_int htr_int, htrunc_c]
      congr 2
      ext x
      congr 2; ring
    rw [hcf_ρ, hcomp_split]
    dsimp only [m_n, v_t]
    push_cast
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination -(((t : ℝ) : ℂ) * ((T.gaussianVariance : ℝ) : ℂ) * (ξ : ℂ) ^ 2 / 2) * hI2
  have hCF_tendsto : ∀ ξ : ℝ, Tendsto (fun n => charFun (μn n) ξ) atTop (𝓝 (charFun μ ξ)) := by
    intro ξ
    rw [hCF ξ, ← EsscherTripletWitnessProp2Aux.levyComplexExponent_I_mul T ξ]
    simp_rw [hCF_μn]
    dsimp only [EsscherTripletWitnessProp2Aux.levyComplexExponent]
    refine Complex.continuous_exp.continuousAt.tendsto.comp ?_
    refine Tendsto.const_mul _ (Tendsto.const_add _ ?_)
    have hint_full : Integrable (EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ))) T.levyMeasure :=
      EsscherTripletWitnessProp2Aux.integrable_expCompIntegrand T hBeta (by simp) (by simp)
    have hind_eq : ∀ n : ℕ,
        (∫ x in A n, EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ)) x ∂T.levyMeasure) =
        ∫ x, (A n).indicator (EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ))) x ∂T.levyMeasure :=
      fun n => (integral_indicator (hA_meas n)).symm
    simp_rw [hind_eq]
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ)) x‖)
      (fun n => (EsscherTripletWitnessProp2Aux.measurable_expCompIntegrand _).indicator (hA_meas n) |>.aestronglyMeasurable)
      hint_full.norm
      (fun n => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
      ?_
    refine ae_of_all _ fun x => ?_
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : EsscherTripletWitnessProp2Aux.expCompIntegrand (Complex.I * (ξ : ℂ)) 0 = 0 := by
        simp [EsscherTripletWitnessProp2Aux.expCompIntegrand]
      have hnot : ∀ n : ℕ, (0 : ℝ) ∉ A n := fun n h => by
        have h1 : (0 : ℝ) < (1 : ℝ) / (n + 1 : ℝ) := by positivity
        have h0r : |(0 : ℝ)| = 0 := abs_zero
        linarith [h.1, h0r]
      simp [h0, hnot]
    · have hpos : 0 < |x| := abs_pos.mpr hx0
      obtain ⟨N1, hN1⟩ := exists_nat_one_div_lt hpos
      obtain ⟨N2, hN2⟩ := exists_nat_gt |x|
      refine tendsto_atTop_of_eventually_const (i₀ := max N1 N2) fun n hn => ?_
      have hxA : x ∈ A n := by
        refine ⟨?_, ?_⟩
        · have hn1_nat : N1 ≤ n := le_trans (le_max_left N1 N2) hn
          have hn1 : (N1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have : (N1 : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).mpr hn1_nat
            linarith
          exact (one_div_le_one_div_of_le (by positivity) hn1).trans hN1.le
        · have hn2_nat : N2 ≤ n := le_trans (le_max_right N1 N2) hn
          have hn2 : (N2 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (N2 : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).mpr hn2_nat
            linarith
          exact hN2.le.trans hn2
      exact Set.indicator_of_mem hxA _
  -- Step 3b: Exponential moment of μn n converges to exp(t * (levyComplexExponent T β).re)
  have hExp_μn : ∀ n : ℕ,
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(μn n)) =
      ENNReal.ofReal (Real.exp ((t : ℝ) *
        (T.drift * β + (T.gaussianVariance : ℝ) * β ^ 2 / 2 +
          (∫ x in A n, (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re ∂T.levyMeasure)))) := by
    intro n
    dsimp only [μn]
    rw [lintegral_exp_addConv]
    have hG_mgf :
        (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(gaussianReal (m_n n) v_t)) =
        ENNReal.ofReal (Real.exp (m_n n * β + (v_t : ℝ) * β ^ 2 / 2)) := by
      have hmgf := congrFun (mgf_id_gaussianReal (μ := m_n n) (v := v_t)) β
      simp only [mgf, id_eq] at hmgf
      have hintG : Integrable (fun x : ℝ => Real.exp (β * x)) (gaussianReal (m_n n) v_t) := by
        by_contra hnot
        have h0 := integral_undef hnot
        rw [hmgf] at h0
        exact (Real.exp_pos _).ne' h0
      rw [← ofReal_integral_eq_lintegral_ofReal hintG (ae_of_all _ fun _ => Real.exp_nonneg _), hmgf]
    have hρ_exp_int : Integrable (fun x : ℝ => Real.exp (β * x)) (ρ n) :=
      (hA_exp_int n β).smul_measure ENNReal.coe_ne_top
    have hρ_fin_lint : ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(ρ n) ≠ ⊤ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hρ_exp_int (ae_of_all _ fun _ => Real.exp_nonneg _)]
      exact ENNReal.ofReal_ne_top
    rw [hG_mgf, lintegral_exp_compoundPoisson (ρ n) β hρ_fin_lint,
      ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
    congr 2
    rw [← ofReal_integral_eq_lintegral_ofReal hρ_exp_int (ae_of_all _ fun _ => Real.exp_nonneg _),
      ENNReal.toReal_ofReal (integral_nonneg fun _ => Real.exp_nonneg _)]
    dsimp only [ρ]
    rw [integral_smul_measure, smul_eq_mul, ENNReal.coe_toReal,
      Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ,
      ENNReal.toReal_mul, ENNReal.coe_toReal]
    have hAn_fin : IsFiniteMeasure (T.levyMeasure.restrict (A n)) := ⟨by
      rw [Measure.restrict_apply_univ]; exact hA_finite n⟩
    have hre_eq : ∀ x : ℝ,
        (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re =
        (Real.exp (β * x) - 1) - β * (if |x| < 1 then x else 0) := by
      intro x
      dsimp only [EsscherTripletWitnessProp2Aux.expCompIntegrand]
      have hexp_c : Complex.exp ((β : ℂ) * (x : ℂ)) = ((Real.exp (β * x) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, Complex.ofReal_exp]
      rw [hexp_c]
      by_cases h : |x| < 1
      · simp only [h, ↓reduceIte, mul_one, Complex.sub_re, Complex.ofReal_re, Complex.one_re,
          Complex.mul_re, Complex.ofReal_im, mul_zero, sub_zero]
      · simp only [h, ↓reduceIte, mul_zero, sub_zero, Complex.sub_re, Complex.ofReal_re,
          Complex.one_re]
    have hre_int :
        (∫ x in A n, (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re ∂T.levyMeasure) =
        (∫ x in A n, Real.exp (β * x) ∂T.levyMeasure) - (T.levyMeasure (A n)).toReal -
          β * (∫ x in A n, (if |x| < 1 then x else 0) ∂T.levyMeasure) := by
      simp_rw [hre_eq]
      have h1 : Integrable (fun x : ℝ => Real.exp (β * x) - 1) (T.levyMeasure.restrict (A n)) :=
        (hA_exp_int n β).sub (integrable_const 1)
      have h2 : Integrable (fun x : ℝ => β * (if |x| < 1 then x else 0)) (T.levyMeasure.restrict (A n)) :=
        (hA_trunc_int n).const_mul β
      rw [integral_sub h1 h2, integral_sub (hA_exp_int n β) (integrable_const 1),
        integral_const, Measure.real_def, Measure.restrict_apply_univ, smul_eq_mul, mul_one,
        integral_const_mul]
    rw [hre_int]
    dsimp only [m_n, v_t]
    push_cast
    ring
  have hExp_tendsto :
      Tendsto (fun n => ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(μn n)) atTop
        (𝓝 (ENNReal.ofReal (Real.exp ((t : ℝ) * (EsscherTripletWitnessProp2Aux.levyComplexExponent T (β : ℂ)).re)))) := by
    simp_rw [hExp_μn]
    have hre_LCE : (EsscherTripletWitnessProp2Aux.levyComplexExponent T (β : ℂ)).re =
        T.drift * β + (T.gaussianVariance : ℝ) * β ^ 2 / 2 +
          ∫ x, (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re ∂T.levyMeasure := by
      dsimp only [EsscherTripletWitnessProp2Aux.levyComplexExponent]
      have hint_β : Integrable (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ)) T.levyMeasure :=
        EsscherTripletWitnessProp2Aux.integrable_expCompIntegrand T hBeta (by simp) (by simp)
      have hre_int : (∫ x, EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x ∂T.levyMeasure).re =
          ∫ x, (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re ∂T.levyMeasure :=
        (Complex.reCLM.integral_comp_comm hint_β).symm
      rw [Complex.add_re, Complex.add_re, hre_int]
      have h1 : ((T.drift : ℂ) * (β : ℂ)).re = T.drift * β := by
        rw [← Complex.ofReal_mul, Complex.ofReal_re]
      have h2 : (((T.gaussianVariance : ℝ) : ℂ) * (β : ℂ) ^ 2 / 2).re =
          (T.gaussianVariance : ℝ) * β ^ 2 / 2 := by
        have : ((T.gaussianVariance : ℝ) : ℂ) * (β : ℂ) ^ 2 / 2 =
            ((((T.gaussianVariance : ℝ) * β ^ 2 / 2 : ℝ) : ℂ)) := by push_cast; ring
        rw [this, Complex.ofReal_re]
      rw [h1, h2]
    rw [hre_LCE]
    refine ENNReal.continuous_ofReal.continuousAt.tendsto.comp ?_
    refine Real.continuous_exp.continuousAt.tendsto.comp ?_
    refine Tendsto.const_mul _ (Tendsto.const_add _ ?_)
    have hint_β : Integrable (fun x => (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re) T.levyMeasure :=
      Complex.reCLM.integrable_comp
        (EsscherTripletWitnessProp2Aux.integrable_expCompIntegrand T hBeta (by simp) (by simp))
    have hind_eq : ∀ n : ℕ,
        (∫ x in A n, (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re ∂T.levyMeasure) =
        ∫ x, (A n).indicator (fun y => (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) y).re) x ∂T.levyMeasure :=
      fun n => (integral_indicator (hA_meas n)).symm
    simp_rw [hind_eq]
    refine tendsto_integral_of_dominated_convergence
      (fun x => ‖(EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) x).re‖)
      (fun n => (Complex.continuous_re.measurable.comp
        (EsscherTripletWitnessProp2Aux.measurable_expCompIntegrand _)).indicator (hA_meas n) |>.aestronglyMeasurable)
      hint_β.norm
      (fun n => ae_of_all _ fun x => norm_indicator_le_norm_self _ _)
      ?_
    refine ae_of_all _ fun x => ?_
    by_cases hx0 : x = 0
    · subst hx0
      have h0 : (EsscherTripletWitnessProp2Aux.expCompIntegrand (β : ℂ) 0).re = 0 := by
        simp [EsscherTripletWitnessProp2Aux.expCompIntegrand]
      have hnot : ∀ n : ℕ, (0 : ℝ) ∉ A n := fun n h => by
        have h1 : (0 : ℝ) < (1 : ℝ) / (n + 1 : ℝ) := by positivity
        have h0r : |(0 : ℝ)| = 0 := abs_zero
        linarith [h.1, h0r]
      simp [h0, hnot]
    · have hpos : 0 < |x| := abs_pos.mpr hx0
      obtain ⟨N1, hN1⟩ := exists_nat_one_div_lt hpos
      obtain ⟨N2, hN2⟩ := exists_nat_gt |x|
      refine tendsto_atTop_of_eventually_const (i₀ := max N1 N2) fun n hn => ?_
      have hxA : x ∈ A n := by
        refine ⟨?_, ?_⟩
        · have hn1_nat : N1 ≤ n := le_trans (le_max_left N1 N2) hn
          have hn1 : (N1 : ℝ) + 1 ≤ (n : ℝ) + 1 := by
            have : (N1 : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).mpr hn1_nat
            linarith
          exact (one_div_le_one_div_of_le (by positivity) hn1).trans hN1.le
        · have hn2_nat : N2 ≤ n := le_trans (le_max_right N1 N2) hn
          have hn2 : (N2 : ℝ) ≤ (n : ℝ) + 1 := by
            have : (N2 : ℝ) ≤ (n : ℝ) := (Nat.cast_le (α := ℝ)).mpr hn2_nat
            linarith
          exact hN2.le.trans hn2
      exact Set.indicator_of_mem hxA _
  -- Step 3c: Pointwise convergence of N(0, 1)-smoothed densities via DCT
  have hdens_tendsto : ∀ x : ℝ,
      Tendsto (fun n => gaussianSmoothDensity (μn n) x) atTop (𝓝 (gaussianSmoothDensity μ x)) := by
    intro x
    simp_rw [gaussianSmoothDensity_eq_fourier]
    refine Tendsto.const_mul _ (Complex.continuous_re.continuousAt.tendsto.comp ?_)
    refine tendsto_integral_of_dominated_convergence
      (fun ξ : ℝ => gaussianPDFReal 0 1 ξ)
      (fun n => by
        have hm_cf : Continuous (charFun (μn n)) := continuous_charFun
        have hm : Measurable (fun ξ : ℝ =>
            (gaussianPDFReal 0 1 ξ : ℂ) * Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I) *
              charFun (μn n) ξ) :=
          ((Complex.continuous_ofReal.measurable.comp (measurable_gaussianPDFReal 0 1)).mul
            (by fun_prop)).mul hm_cf.measurable
        exact hm.aestronglyMeasurable)
      (integrable_gaussianPDFReal 0 1)
      (fun n => ae_of_all _ fun ξ => by
        rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (gaussianPDFReal_nonneg 0 1 ξ)]
        have h1 : ‖Complex.exp (-(ξ : ℂ) * (x : ℂ) * Complex.I)‖ = 1 := by
          have : -(ξ : ℂ) * (x : ℂ) * Complex.I = (((-(ξ * x) : ℝ) : ℂ) * Complex.I) := by push_cast; ring
          rw [this, Complex.norm_exp_ofReal_mul_I]
        rw [h1, mul_one]
        calc gaussianPDFReal 0 1 ξ * ‖charFun (μn n) ξ‖
            ≤ gaussianPDFReal 0 1 ξ * 1 :=
              mul_le_mul_of_nonneg_left (norm_charFun_le_one ξ) (gaussianPDFReal_nonneg 0 1 ξ)
          _ = gaussianPDFReal 0 1 ξ := mul_one _)
      (ae_of_all _ fun ξ => (hCF_tendsto ξ).const_mul _)
  -- Step 3d: Fatou's lemma -> finite exponential lintegral -> Integrable
  have hfatou :
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianSmoothDensity μ x) ∂volume) ≤
      liminf (fun n => ∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) *
        ENNReal.ofReal (gaussianSmoothDensity (μn n) x) ∂volume) atTop := by
    have hpt : ∀ x : ℝ,
        ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianSmoothDensity μ x) =
        liminf (fun n => ENNReal.ofReal (Real.exp (β * x)) *
          ENNReal.ofReal (gaussianSmoothDensity (μn n) x)) atTop := fun x => by
      have ht : Tendsto (fun n => ENNReal.ofReal (Real.exp (β * x)) *
          ENNReal.ofReal (gaussianSmoothDensity (μn n) x)) atTop
          (𝓝 (ENNReal.ofReal (Real.exp (β * x)) * ENNReal.ofReal (gaussianSmoothDensity μ x))) :=
        ENNReal.Tendsto.const_mul (ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hdens_tendsto x))
          (Or.inr ENNReal.ofReal_ne_top)
      exact ht.liminf_eq.symm
    simp_rw [hpt]
    refine lintegral_liminf_le' fun n => ?_
    have hm1 : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (β * x))) := by fun_prop
    have hm2 : Measurable (fun x : ℝ => ENNReal.ofReal (gaussianSmoothDensity (μn n) x)) := by
      have hcont : Measurable (fun x : ℝ => ∫ y, gaussianPDFReal 0 1 (x - y) ∂(μn n)) := by
        have hpm : StronglyMeasurable (Function.uncurry fun x y => gaussianPDFReal 0 1 (x - y)) :=
          ((measurable_gaussianPDFReal 0 1).comp measurable_sub).stronglyMeasurable
        exact hpm.integral_prod_right.measurable
      exact ENNReal.measurable_ofReal.comp hcont
    exact (hm1.mul hm2).aemeasurable
  simp_rw [lintegral_exp_mul_gaussianSmoothDensity] at hfatou
  have hrhs_tendsto :
      Tendsto (fun n => (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂(μn n)) *
          ENNReal.ofReal (Real.exp (β ^ 2 / 2))) atTop
        (𝓝 (ENNReal.ofReal (Real.exp ((t : ℝ) * (EsscherTripletWitnessProp2Aux.levyComplexExponent T (β : ℂ)).re)) *
          ENNReal.ofReal (Real.exp (β ^ 2 / 2)))) :=
    ENNReal.Tendsto.mul_const hExp_tendsto (Or.inr ENNReal.ofReal_ne_top)
  rw [hrhs_tendsto.liminf_eq] at hfatou
  have hlt_top_mul :
      (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂μ) * ENNReal.ofReal (Real.exp (β ^ 2 / 2)) < ⊤ :=
    lt_of_le_of_lt hfatou (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top)
  have hlt_top : (∫⁻ x, ENNReal.ofReal (Real.exp (β * x)) ∂μ) < ⊤ := by
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.top_mul (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'] at hlt_top_mul
    exact (lt_irrefl ⊤) hlt_top_mul
  refine ⟨(by fun_prop : Measurable (fun x : ℝ => Real.exp (β * x))).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm]
  have heq : (fun x : ℝ => ‖Real.exp (β * x)‖ₑ) = fun x : ℝ => ENNReal.ofReal (Real.exp (β * x)) := by
    ext x; rw [Real.enorm_eq_ofReal (Real.exp_nonneg _)]
  simpa only [heq] using hlt_top

/-! ### Part 4: Independence of future increments from the completed natural filtration -/

private lemma fin_partial_sum_increments
    {Omega : Type} (X : NNReal → Omega → ℝ) (h0 : X 0 = fun _ => 0)
    {k : ℕ} (e : Fin (k + 1) → NNReal) (he0 : e 0 = 0) (i : Fin (k + 1)) (ω : Omega) :
    X (e i) ω =
      ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.castSucc < i),
        ProbabilityTheory.increment X (e j.castSucc) (e j.succ) ω := by
  induction i using Fin.induction with
  | zero =>
    have hfilt : Finset.univ.filter (fun j : Fin k => j.castSucc < (0 : Fin (k + 1))) = ∅ := by
      ext j; simp
    rw [hfilt, Finset.sum_empty, he0, h0]
  | succ i' ih =>
    have hfilt :
        Finset.univ.filter (fun j : Fin k => j.castSucc < i'.succ) =
        insert i' (Finset.univ.filter (fun j : Fin k => j.castSucc < i'.castSucc)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro h
        rcases lt_or_eq_of_le (Fin.le_castSucc_iff.mpr h) with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl (Fin.castSucc_injective k heq)
      · rintro (rfl | hlt)
        · exact Fin.castSucc_lt_succ
        · exact hlt.trans Fin.castSucc_lt_succ
    have hnot : i' ∉ Finset.univ.filter (fun j : Fin k => j.castSucc < i'.castSucc) := by simp
    rw [hfilt, Finset.sum_insert hnot, ← ih]
    dsimp only [ProbabilityTheory.increment]
    ring

private lemma indep_increment_natFiltr
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    {s t : NNReal} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance)
      (PerfCorrMSQ.natFiltr X s) P := by
  have hX_meas : ∀ u : NNReal, Measurable (X u) :=
    EsscherTripletWitnessProp2Aux.measurable_X P F X hNatural
  have hinc_meas : Measurable (ProbabilityTheory.increment X s t) :=
    (hX_meas t).sub (hX_meas s)
  have hnat_le : PerfCorrMSQ.natFiltr X s ≤ mΩ := by
    refine le_trans ?_ (F.le s)
    rw [hNatural s]
    exact le_sup_left
  let p1 : Set (Set Omega) :=
    {A | MeasurableSet[MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance] A}
  let p2 : Set (Set Omega) :=
    {C | ∃ (U : Finset NNReal), (∀ u ∈ U, u ≤ s) ∧
      ∃ (B : NNReal → Set ℝ), (∀ u ∈ U, MeasurableSet (B u)) ∧
        C = ⋂ u ∈ U, X u ⁻¹' B u}
  have hp1_pi : IsPiSystem p1 := fun s1 hs1 s2 hs2 _ =>
    @MeasurableSet.inter _ (MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance) _ _ hs1 hs2
  have hp1_gen : MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance =
      MeasurableSpace.generateFrom p1 :=
    (@MeasurableSpace.generateFrom_measurableSet Omega
      (MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance)).symm
  have hp2_pi : IsPiSystem p2 := by
    rintro C1 ⟨U1, hU1, B1, hB1, rfl⟩ C2 ⟨U2, hU2, B2, hB2, rfl⟩ _
    classical
    refine ⟨U1 ∪ U2, fun u hu => by
        rcases Finset.mem_union.mp hu with h | h
        · exact hU1 u h
        · exact hU2 u h,
      fun u => (if u ∈ U1 then B1 u else Set.univ) ∩ (if u ∈ U2 then B2 u else Set.univ),
      fun u _ => MeasurableSet.inter (by split_ifs with h1; exact hB1 u h1; exact MeasurableSet.univ)
        (by split_ifs with h2; exact hB2 u h2; exact MeasurableSet.univ), ?_⟩
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, Finset.mem_union]
    constructor
    · rintro ⟨h1, h2⟩ u _
      exact ⟨by split_ifs with hu1; exact h1 u hu1; trivial,
        by split_ifs with hu2; exact h2 u hu2; trivial⟩
    · intro h
      refine ⟨fun u hu1 => ?_, fun u hu2 => ?_⟩
      · have := (h u (Or.inl hu1)).1
        rwa [if_pos hu1] at this
      · have := (h u (Or.inr hu2)).2
        rwa [if_pos hu2] at this
  have hp2_gen : PerfCorrMSQ.natFiltr X s = MeasurableSpace.generateFrom p2 := by
    refine le_antisymm ?_ ?_
    · refine iSup₂_le fun u hu => ?_
      intro A ⟨B, hB, hAB⟩
      rw [← hAB]
      exact MeasurableSpace.measurableSet_generateFrom
        ⟨{u}, fun v hv => by simp_all, fun _ => B, fun _ _ => hB, by simp⟩
    · refine MeasurableSpace.generateFrom_le ?_
      rintro C ⟨U, hU, B, hB, rfl⟩
      refine MeasurableSet.biInter U.countable_toSet fun u hu => ?_
      have hmeas_u : Measurable[PerfCorrMSQ.natFiltr X s] (X u) := by
        rw [measurable_iff_comap_le]
        exact le_iSup₂_of_le u (hU u hu) le_rfl
      exact hmeas_u (hB u hu)
  refine IndepSets.indep (measurable_iff_comap_le.mp hinc_meas) hnat_le hp1_pi hp2_pi hp1_gen hp2_gen ?_
  rw [IndepSets_iff]
  rintro A C hA ⟨U, hU, B, hB, rfl⟩
  classical
  let S₀ : Finset NNReal := insert 0 (insert s U)
  have hS₀_pos : S₀.card ≠ 0 := Finset.card_ne_zero.mpr ⟨0, Finset.mem_insert_self _ _⟩
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hS₀_pos
  let e : Fin (k + 1) ↪o NNReal := S₀.orderEmbOfFin hk
  have he_mem : ∀ i : Fin (k + 1), e i ∈ S₀ := fun i => Finset.orderEmbOfFin_mem S₀ hk i
  have he0 : e 0 = 0 := by
    have h0_mem : (0 : NNReal) ∈ S₀ := Finset.mem_insert_self _ _
    have hle : e 0 ≤ 0 := by
      obtain ⟨i, hi⟩ : ∃ i, e i = 0 := by
        have hrange : Set.range e = (S₀ : Set NNReal) := Finset.range_orderEmbOfFin S₀ hk
        have : (0 : NNReal) ∈ Set.range e := by rw [hrange]; exact h0_mem
        exact this
      rw [← hi]
      exact e.monotone (Fin.zero_le i)
    exact le_antisymm hle (zero_le : (0 : NNReal) ≤ e 0)
  have helast : e (Fin.last k) = s := by
    have hs_mem : s ∈ S₀ := Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)
    have hle_s : e (Fin.last k) ≤ s := by
      have hm := he_mem (Fin.last k)
      simp only [S₀, Finset.mem_insert] at hm
      rcases hm with h | h | h
      · rw [h]; exact (zero_le : (0 : NNReal) ≤ s)
      · rw [h]
      · exact hU _ h
    have hs_le : s ≤ e (Fin.last k) := by
      have hrange : Set.range e = (S₀ : Set NNReal) := Finset.range_orderEmbOfFin S₀ hk
      have : s ∈ Set.range e := by rw [hrange]; exact hs_mem
      rcases this with ⟨i, hi⟩
      rw [← hi]
      exact e.monotone (Fin.le_last i)
    exact le_antisymm hle_s hs_le
  let tp : Fin (k + 2) → NNReal := Fin.snoc (fun i => e i) t
  have htp_mono : Monotone tp := by
    intro i j hij
    cases i using Fin.lastCases with
    | last =>
      have hj : j = Fin.last (k + 1) := le_antisymm (Fin.le_last j) hij
      subst hj; exact le_rfl
    | cast i' =>
      cases j using Fin.lastCases with
      | last =>
        simp only [tp, Fin.snoc_castSucc, Fin.snoc_last]
        exact (e.monotone (Fin.le_last i')).trans (helast.le.trans hst)
      | cast j' =>
        simp only [tp, Fin.snoc_castSucc]
        exact e.monotone (Fin.castSucc_le_castSucc_iff.mp hij)
  let V : Fin (k + 1) → Omega → ℝ := fun j =>
    ProbabilityTheory.increment X (tp j.castSucc) (tp j.succ)
  have hV_indep : iIndepFun V P := hX.indep_increments (k + 1) tp htp_mono
  have hV_le : ∀ j : Fin (k + 1), MeasurableSpace.comap (V j) inferInstance ≤ mΩ := fun j =>
    measurable_iff_comap_le.mp ((hX_meas _).sub (hX_meas _))
  have hind_sup :
      Indep (⨆ j ∈ ({Fin.last k} : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance)
        (⨆ j ∈ ({Fin.last k}ᶜ : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance) P :=
    indep_iSup_of_disjoint hV_le hV_indep disjoint_compl_right
  have hV_last : V (Fin.last k) = ProbabilityTheory.increment X s t := by
    ext ω
    dsimp only [V, tp]
    rw [Fin.snoc_castSucc, helast]
    have hsucc_last : (Fin.last k).succ = Fin.last (k + 1) := rfl
    rw [hsucc_last, Fin.snoc_last]
  have hA_in : MeasurableSet[⨆ j ∈ ({Fin.last k} : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance] A := by
    have hle : MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance ≤
        ⨆ j ∈ ({Fin.last k} : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance := by
      rw [← hV_last]
      exact le_iSup₂_of_le (Fin.last k) (Set.mem_singleton _) le_rfl
    exact hle A hA
  have hC_in : MeasurableSet[⨆ j ∈ ({Fin.last k}ᶜ : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance]
      (⋂ u ∈ U, X u ⁻¹' B u) := by
    refine MeasurableSet.biInter U.countable_toSet fun u hu => ?_
    have hu_range : u ∈ Set.range e := by
      rw [Finset.range_orderEmbOfFin S₀ hk]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu)
    rcases hu_range with ⟨i, rfl⟩
    have hmeas_Xi : Measurable[⨆ j ∈ ({Fin.last k}ᶜ : Set (Fin (k + 1))), MeasurableSpace.comap (V j) inferInstance]
        (X (e i)) := by
      have heq : X (e i) = fun ω =>
          ∑ j ∈ Finset.univ.filter (fun j : Fin k => j.castSucc < i), V j.castSucc ω := by
        ext ω
        rw [fin_partial_sum_increments X hX.start_zero e he0 i ω]
        refine Finset.sum_congr rfl fun j _ => ?_
        dsimp only [V, tp]
        have h2 : j.castSucc.succ = j.succ.castSucc := rfl
        rw [h2, Fin.snoc_castSucc, Fin.snoc_castSucc]
      rw [heq]
      refine Finset.measurable_sum _ fun j _ => ?_
      rw [measurable_iff_comap_le]
      exact le_iSup₂_of_le j.castSucc (Fin.castSucc_ne_last j) le_rfl
    exact hmeas_Xi (hB (e i) hu)
  rw [Indep_iff] at hind_sup
  exact hind_sup A (⋂ u ∈ U, X u ⁻¹' B u) hA_in hC_in

private lemma indep_increment_completedFiltration
    {Omega : Type} [mΩ : MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal mΩ)
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : Kyprianou.Ch03.IsCompletedNaturalFiltration P X F)
    {s t : NNReal} (hst : s ≤ t) :
    Indep (MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance) (F s) P := by
  have hind_nat := indep_increment_natFiltr P F X hX hNatural hst
  let approxMS : MeasurableSpace Omega :=
    { MeasurableSet' := fun A => ∃ A' : Set Omega, MeasurableSet[PerfCorrMSQ.natFiltr X s] A' ∧ A =ᵐ[P] A'
      measurableSet_empty := ⟨∅, @MeasurableSet.empty _ (PerfCorrMSQ.natFiltr X s), EventuallyEq.rfl⟩
      measurableSet_compl := fun A ⟨A', hA', hAE⟩ => by
        have hA'c : MeasurableSet[PerfCorrMSQ.natFiltr X s] A'ᶜ := hA'.compl
        exact ⟨A'ᶜ, hA'c, hAE.compl⟩
      measurableSet_iUnion := fun f hf => by
        choose g hg hAE using hf
        refine ⟨⋃ n, g n, @MeasurableSet.iUnion _ _ (PerfCorrMSQ.natFiltr X s) _ _ hg, ?_⟩
        filter_upwards [ae_all_iff.mpr hAE] with ω hω
        change (ω ∈ ⋃ n, f n) = (ω ∈ ⋃ n, g n)
        simp only [Set.mem_iUnion]
        exact propext (exists_congr fun n => eq_iff_iff.mp (hω n)) }
  have hFs_le : F s ≤ approxMS := by
    rw [hNatural s]
    refine sup_le (fun A hA => ⟨A, hA, EventuallyEq.rfl⟩) (MeasurableSpace.generateFrom_le ?_)
    rintro A ⟨N, _, hPN, hAN⟩
    refine ⟨∅, @MeasurableSet.empty _ (PerfCorrMSQ.natFiltr X s), ?_⟩
    have hPA : P A = 0 := measure_mono_null hAN hPN
    exact ae_eq_empty.mpr hPA
  rw [Indep_iff] at hind_nat ⊢
  intro E A hE hA
  rcases hFs_le A hA with ⟨A', hA', hAE⟩
  have hEA : (E ∩ A : Set Omega) =ᵐ[P] (E ∩ A' : Set Omega) := by
    filter_upwards [hAE] with ω hω
    change (ω ∈ E ∩ A) = (ω ∈ E ∩ A')
    simp only [Set.mem_inter_iff]
    exact propext (and_congr_right fun _ => eq_iff_iff.mp hω)
  rw [measure_congr hEA, measure_congr hAE]
  exact hind_nat E A' hE hA'

end EsscherTimeConsistencyAux

open Kyprianou.Ch03 EsscherTripletWitnessProp2Aux EsscherTimeConsistencyAux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : ℝ)
    (hBeta : IntegrableOn (fun x : ℝ => Real.exp (beta * x))
      {x : ℝ | 1 ≤ |x|} T.levyMeasure) :
    let k := Real.log (∫ omega, Real.exp (beta * X 1 omega) ∂P)
    (∀ s t : NNReal, s ≤ t →
      ∀ A : Set Omega, MeasurableSet[F s] A →
        (∫ omega, Set.indicator A (esscherDensity X beta k t) omega ∂P) =
        (∫ omega, Set.indicator A (esscherDensity X beta k s) omega ∂P)) := by
  intro k
  have hX_meas : ∀ u : NNReal, Measurable (X u) :=
    EsscherTripletWitnessProp2Aux.measurable_X P F X hNatural
  have hX_measF : ∀ u : NNReal, Measurable[F u] (X u) :=
    EsscherTripletWitnessProp2Aux.measurable_X_F P F X hNatural
  -- Step 1: Exponential integrability of X_u under P for all u : NNReal
  have hExp_int_map : ∀ u : NNReal, Integrable (fun x : ℝ => Real.exp (beta * x)) (P.map (X u)) := by
    intro u
    have : IsProbabilityMeasure (P.map (X u)) := Measure.isProbabilityMeasure_map (hX_meas u).aemeasurable
    exact EsscherTimeConsistencyAux.exp_integrable_of_charFun_levyKhintchine
      (P.map (X u)) T u beta (hLK u) hBeta
  have hExp_int : ∀ u : NNReal, Integrable (fun ω => Real.exp (beta * X u ω)) P := fun u =>
    (integrable_map_measure (by fun_prop : Measurable (fun x : ℝ => Real.exp (beta * x))).aestronglyMeasurable
      (hX_meas u).aemeasurable).mp (hExp_int_map u)
  -- Step 2: Exact MGF identity ∫ exp(beta * X_u) dP = exp(u * (levyComplexExponent T beta).re)
  have hExp_val : ∀ u : NNReal,
      (∫ ω, Real.exp (beta * X u ω) ∂P) =
      Real.exp ((u : ℝ) * (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).re) := by
    intro u
    by_cases hβ0 : beta = 0
    · subst hβ0
      have hlce0 : EsscherTripletWitnessProp2Aux.levyComplexExponent T (0 : ℂ) = 0 := by
        simp [EsscherTripletWitnessProp2Aux.levyComplexExponent,
          EsscherTripletWitnessProp2Aux.expCompIntegrand]
      simp [hlce0]
    have : IsProbabilityMeasure (P.map (X u)) := Measure.isProbabilityMeasure_map (hX_meas u).aemeasurable
    let μu := P.map (X u)
    let g : ℂ → ℂ := fun z =>
      (∫ x, Complex.exp (z * (x : ℂ)) ∂μu) -
        Complex.exp (((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T z)
    have hcont : ContinuousOn g {z : ℂ | min 0 beta ≤ z.re ∧ z.re ≤ max 0 beta} := by
      have hc1 := EsscherTripletWitnessProp2Aux.continuousOn_bilateralLaplace (hExp_int_map u)
      have hc2 : ContinuousOn (fun z : ℂ =>
          Complex.exp (((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T z))
          {z : ℂ | min 0 beta ≤ z.re ∧ z.re ≤ max 0 beta} :=
        Complex.continuous_exp.comp_continuousOn
          ((EsscherTripletWitnessProp2Aux.continuousOn_levyComplexExponent T hBeta).const_mul _)
      exact hc1.sub hc2
    have hdiff : DifferentiableOn ℂ g {z : ℂ | min 0 beta < z.re ∧ z.re < max 0 beta} := by
      have hd1 := EsscherTripletWitnessProp2Aux.differentiableOn_bilateralLaplace (hExp_int_map u)
      have hd2 : DifferentiableOn ℂ (fun z : ℂ =>
          Complex.exp (((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T z))
          {z : ℂ | min 0 beta < z.re ∧ z.re < max 0 beta} :=
        ((EsscherTripletWitnessProp2Aux.differentiableOn_levyComplexExponent T hBeta).const_mul _).cexp
      exact hd1.sub hd2
    have himag : ∀ y : ℝ, g ((y : ℂ) * Complex.I) = 0 := fun y => by
      dsimp only [g]
      have hcf_eq : (∫ x, Complex.exp (((y : ℂ) * Complex.I) * (x : ℂ)) ∂μu) = charFun μu y := by
        rw [charFun_apply_real]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        ring_nf
      have hI : ((y : ℂ) * Complex.I) = Complex.I * (y : ℂ) := mul_comm _ _
      rw [hcf_eq, hI, EsscherTripletWitnessProp2Aux.levyComplexExponent_I_mul T y, hLK u y, sub_self]
    have hzero := EsscherTripletWitnessProp2Aux.eq_zero_on_uIcc_strip_of_eq_zero_on_imag_axis
      hβ0 hcont hdiff himag (beta : ℂ) (by simp) (by simp)
    have heq_c : (∫ x, Complex.exp ((beta : ℂ) * (x : ℂ)) ∂μu) =
        Complex.exp (((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)) :=
      sub_eq_zero.mp hzero
    have hre := congrArg Complex.re heq_c
    have hlhs : (∫ x, Complex.exp ((beta : ℂ) * (x : ℂ)) ∂μu).re =
        ∫ ω, Real.exp (beta * X u ω) ∂P := by
      have hcast : ∀ x : ℝ, Complex.exp ((beta : ℂ) * (x : ℂ)) = Complex.ofRealCLM (Real.exp (beta * x)) := fun x => by
        change Complex.exp ((beta : ℂ) * (x : ℂ)) = ((Real.exp (beta * x) : ℝ) : ℂ)
        rw [← Complex.ofReal_mul, Complex.ofReal_exp]
      simp_rw [hcast]
      rw [Complex.ofRealCLM.integral_comp_comm (hExp_int_map u)]
      change (∫ x, Real.exp (beta * x) ∂(P.map (X u))) = _
      rw [integral_map (hX_meas u).aemeasurable (by fun_prop : Measurable (fun x : ℝ => Real.exp (beta * x))).aestronglyMeasurable]
    have hrhs : (Complex.exp (((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ))).re =
        Real.exp ((u : ℝ) * (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).re) := by
      have him : (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).im = 0 :=
        EsscherTripletWitnessProp2Aux.levyComplexExponent_ofReal_im T beta
      have hreal : ((u : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ) =
          ((((u : ℝ) * (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).re : ℝ) : ℂ)) := by
        apply Complex.ext
        · simp [him]
        · simp [him]
      rw [hreal, ← Complex.ofReal_exp, Complex.ofReal_re]
    rw [hlhs, hrhs] at hre
    exact hre
  -- Step 3: k = (levyComplexExponent T beta).re and unit mean of esscherDensity at all times u
  have hk_eq : k = (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).re := by
    dsimp only [k]
    rw [hExp_val 1]
    simp
  have hDens_int : ∀ u : NNReal, Integrable (esscherDensity X beta k u) P := fun u => by
    have hfac : esscherDensity X beta k u = fun ω => Real.exp (-(k * (u : ℝ))) * Real.exp (beta * X u ω) := by
      ext ω; dsimp only [esscherDensity]; rw [← Real.exp_add]; congr 1; ring
    rw [hfac]
    exact (hExp_int u).const_mul _
  have hDens_unit : ∀ u : NNReal,
      (∫⁻ ω, ENNReal.ofReal (esscherDensity X beta k u ω) ∂P) = 1 := fun u => by
    rw [← ofReal_integral_eq_lintegral_ofReal (hDens_int u) (ae_of_all _ fun _ => Real.exp_nonneg _)]
    have hfac : esscherDensity X beta k u = fun ω => Real.exp (-(k * (u : ℝ))) * Real.exp (beta * X u ω) := by
      ext ω; dsimp only [esscherDensity]; rw [← Real.exp_add]; congr 1; ring
    rw [hfac, integral_const_mul, hExp_val u, ← hk_eq, ← Real.exp_add]
    have h0 : -(k * (u : ℝ)) + (u : ℝ) * k = 0 := by ring
    rw [h0, Real.exp_zero, ENNReal.ofReal_one]
  -- Step 4: Density time consistency via independence of X_t - X_s from F_s + stationary increments
  intro s t hst A hA
  have hA_m : MeasurableSet A := F.le s A hA
  have hpos_t : 0 ≤ ∫ ω, A.indicator (esscherDensity X beta k t) ω ∂P :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) ω
  have hpos_s : 0 ≤ ∫ ω, A.indicator (esscherDensity X beta k s) ω ∂P :=
    integral_nonneg fun ω => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) ω
  rw [← ENNReal.ofReal_eq_ofReal_iff hpos_t hpos_s]
  rw [ofReal_integral_eq_lintegral_ofReal ((hDens_int t).indicator hA_m)
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) ω),
    ofReal_integral_eq_lintegral_ofReal ((hDens_int s).indicator hA_m)
      (ae_of_all _ fun ω => Set.indicator_nonneg (fun _ _ => Real.exp_nonneg _) ω)]
  have hsplit : ∀ ω : Omega,
      ENNReal.ofReal (A.indicator (esscherDensity X beta k t) ω) =
      ENNReal.ofReal (Real.exp (beta * ProbabilityTheory.increment X s t ω - k * ((t : ℝ) - (s : ℝ)))) *
        ENNReal.ofReal (A.indicator (esscherDensity X beta k s) ω) := by
    intro ω
    by_cases hmem : ω ∈ A
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
      dsimp only [esscherDensity, ProbabilityTheory.increment]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2; ring
    · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, ENNReal.ofReal_zero, mul_zero]
  simp_rw [hsplit]
  have hind := EsscherTimeConsistencyAux.indep_increment_completedFiltration P F X hX hNatural hst
  have hinc_meas : Measurable (ProbabilityTheory.increment X s t) := (hX_meas t).sub (hX_meas s)
  have hf_meas : Measurable[MeasurableSpace.comap (ProbabilityTheory.increment X s t) inferInstance]
      (fun ω => ENNReal.ofReal (Real.exp (beta * ProbabilityTheory.increment X s t ω - k * ((t : ℝ) - (s : ℝ))))) :=
    (by fun_prop : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * ((t : ℝ) - (s : ℝ)))))).comp
      (Measurable.of_comap_le le_rfl)
  have hg_meas : Measurable[F s]
      (fun ω => ENNReal.ofReal (A.indicator (esscherDensity X beta k s) ω)) := by
    have hds : Measurable[F s] (esscherDensity X beta k s) :=
      Real.measurable_exp.comp (((hX_measF s).const_mul beta).sub measurable_const)
    exact ENNReal.measurable_ofReal.comp (hds.indicator hA)
  rw [lintegral_mul_eq_lintegral_mul_lintegral_of_independent_measurableSpace
    (measurable_iff_comap_le.mp hinc_meas) (F.le s) hind hf_meas hg_meas]
  let d : NNReal := t - s
  have hd_add : s + d = t := add_tsub_cancel_of_le hst
  have hd_coe : (t : ℝ) - (s : ℝ) = (d : ℝ) := (NNReal.coe_sub hst).symm
  have hinc_unit :
      (∫⁻ ω, ENNReal.ofReal (Real.exp (beta * ProbabilityTheory.increment X s t ω - k * ((t : ℝ) - (s : ℝ)))) ∂P) = 1 := by
    rw [hd_coe, ← hd_add]
    have hgm : Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * (d : ℝ)))) := by fun_prop
    have hinc_sd_meas : Measurable (ProbabilityTheory.increment X s (s + d)) :=
      (hX_meas (s + d)).sub (hX_meas s)
    have hinc_0d_meas : Measurable (ProbabilityTheory.increment X 0 d) :=
      (hX_meas d).sub (hX_meas 0)
    have hstat := hX.stationary_increments s d
    rw [← lintegral_map hgm hinc_sd_meas, hstat.map_eq, lintegral_map hgm hinc_0d_meas]
    have h0eq : ∀ ω : Omega, ProbabilityTheory.increment X 0 d ω = X d ω := fun ω => by
      simp [ProbabilityTheory.increment, hX.start_zero]
    simp_rw [h0eq]
    exact hDens_unit d
  rw [hinc_unit, one_mul]
