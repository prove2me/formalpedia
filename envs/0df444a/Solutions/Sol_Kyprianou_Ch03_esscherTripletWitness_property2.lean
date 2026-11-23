-- Prove2me | solution 1 for Kyprianou.Ch03.esscherTripletWitness_property2
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-23T11:18:48.84326+00:00
-- url     : https://prove2.me/submissions/4b56aa5b-bdf6-4da7-bafd-e53a3692da5a

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

open Kyprianou.Ch03 EsscherTripletWitnessProp2Aux

theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P Q : Measure Omega) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (F : Filtration NNReal (inferInstance : MeasurableSpace Omega))
    (X : NNReal -> Omega -> Real)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (hNatural : IsCompletedNaturalFiltration P X F)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : forall (t : NNReal) (xi : Real),
      charFun (P.map (X t)) xi =
        Complex.exp ((((t : Real) : Complex)) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (beta : Real)
    (hBeta : IntegrableOn
      (fun x : Real => Real.exp (beta * x))
      {x : Real | 1 <= abs x} T.levyMeasure)
    (hEsscher : forall (t : NNReal) (A : Set Omega),
      MeasurableSet[F t] A ->
      Q A =
        ENNReal.ofReal
          (∫ omega, Set.indicator A
            (fun omega : Omega =>
              esscherDensity X beta
                (Real.log
                  (∫ eta, Real.exp (beta * X 1 eta) ∂P))
                t omega) omega ∂P)) :
    forall (Tbeta : ProbabilityTheory.LevyKhintchineTriple),
      (Tbeta.drift =
        T.drift + beta * (T.gaussianVariance : Real) +
          ∫ x in {x : Real | abs x < 1},
            (Real.exp (beta * x) - 1) * x ∂T.levyMeasure ∧ Tbeta.gaussianVariance = T.gaussianVariance ∧ Tbeta.levyMeasure =
        T.levyMeasure.withDensity
          (fun x : Real => ENNReal.ofReal (Real.exp (beta * x)))) ->
      (forall (t : NNReal) (xi : Real),
        charFun (Q.map (X t)) xi =
          Complex.exp ((((t : Real) : Complex)) *
            Kyprianou.Ch01.levyTripleExponent Tbeta xi)) := by
  let _ := hX
  set k : ℝ := Real.log (∫ eta, Real.exp (beta * X 1 eta) ∂P)
  have hX_measF : ∀ t : NNReal, Measurable[F t] (X t) :=
    EsscherTripletWitnessProp2Aux.measurable_X_F P F X hNatural
  have hX_meas : ∀ t : NNReal, Measurable (X t) :=
    EsscherTripletWitnessProp2Aux.measurable_X P F X hNatural
  -- Step 1: Normalization & integrability of the Esscher density at every t
  have hDens_int_eq_one : ∀ t : NNReal,
      (∫ omega, esscherDensity X beta k t omega ∂P) = 1 := by
    intro t
    have h1 := hEsscher t Set.univ MeasurableSet.univ
    simp only [measure_univ, Set.indicator_univ] at h1
    have hpos : 0 ≤ ∫ omega, esscherDensity X beta k t omega ∂P :=
      integral_nonneg fun omega => Real.exp_nonneg _
    have hofReal : ENNReal.ofReal (∫ omega, esscherDensity X beta k t omega ∂P) =
        ENNReal.ofReal 1 := by simpa using h1.symm
    exact (ENNReal.ofReal_eq_ofReal_iff hpos zero_le_one).mp hofReal
  have hDens_integrable : ∀ t : NNReal,
      Integrable (esscherDensity X beta k t) P := by
    intro t
    by_contra hnot
    have h0 : (∫ omega, esscherDensity X beta k t omega ∂P) = 0 := integral_undef hnot
    linarith [hDens_int_eq_one t]
  have hExp_integrable_P : ∀ t : NNReal,
      Integrable (fun omega => Real.exp (beta * X t omega)) P := by
    intro t
    have heq : (fun omega => Real.exp (beta * X t omega)) =
        fun omega => Real.exp (k * (t : ℝ)) * esscherDensity X beta k t omega := by
      ext omega
      unfold esscherDensity
      rw [← Real.exp_add]
      ring_nf
    rw [heq]
    exact (hDens_integrable t).const_mul _
  have hExp_integrable_map : ∀ t : NNReal,
      Integrable (fun x : ℝ => Real.exp (beta * x)) (P.map (X t)) := by
    intro t
    exact (integrable_map_measure
      (by fun_prop : Measurable (fun x : ℝ => Real.exp (beta * x))).aestronglyMeasurable
      (hX_meas t).aemeasurable).mpr (hExp_integrable_P t)
  -- Step 2: Law of X t under Q is the exponentially tilted pushforward of P.map (X t)
  have hQ_map : ∀ t : NNReal,
      Q.map (X t) = (P.map (X t)).withDensity
        (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * (t : ℝ)))) := by
    intro t
    ext B hB
    rw [Measure.map_apply (hX_meas t) hB,
      withDensity_apply _ hB,
      setLIntegral_map hB (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * (t : ℝ)))) by fun_prop) (hX_meas t)]
    have hA_measF : MeasurableSet[F t] (X t ⁻¹' B) := hX_measF t hB
    rw [hEsscher t (X t ⁻¹' B) hA_measF]
    have hA_meas : MeasurableSet (X t ⁻¹' B) := hX_meas t hB
    rw [integral_indicator hA_meas]
    have hint_restrict : IntegrableOn (esscherDensity X beta k t) (X t ⁻¹' B) P :=
      (hDens_integrable t).integrableOn
    rw [ofReal_integral_eq_lintegral_ofReal hint_restrict
      (ae_of_all _ fun omega => Real.exp_nonneg _)]
    rfl
  -- Step 3: Express charFun (Q.map (X t)) xi in terms of the bilateral Laplace transform
  have hcharFun_Q : ∀ (t : NNReal) (xi : ℝ),
      charFun (Q.map (X t)) xi =
        Complex.exp (-((k : ℂ) * ((t : ℝ) : ℂ))) *
          ∫ x, Complex.exp ((((beta : ℂ) + I * (xi : ℂ)) * (x : ℂ))) ∂(P.map (X t)) := by
    intro t xi
    rw [hQ_map t, charFun_apply_real]
    rw [integral_withDensity_eq_integral_toReal_smul
      (show Measurable (fun x : ℝ => ENNReal.ofReal (Real.exp (beta * x - k * (t : ℝ)))) by fun_prop)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [ENNReal.toReal_ofReal (Real.exp_nonneg _), Complex.real_smul, Complex.ofReal_exp,
      ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  intro Tbeta ⟨hDrift, hVar, hLevy⟩ t xi
  -- Case split on beta = 0 vs beta ≠ 0
  by_cases hβ0 : beta = 0
  · subst hβ0
    have hTbeta_eq : Kyprianou.Ch01.levyTripleExponent Tbeta xi =
        Kyprianou.Ch01.levyTripleExponent T xi := by
      unfold Kyprianou.Ch01.levyTripleExponent
      rw [hDrift, hVar, hLevy]
      simp
    have hk0 : k = 0 := by
      dsimp only [k]
      simp
    have hQ_eq : Q.map (X t) = P.map (X t) := by
      rw [hQ_map t, hk0]
      simp
    rw [hQ_eq, hTbeta_eq, hLK t xi]
  · -- Main case beta ≠ 0: analytic continuation on the closed strip between 0 and beta
    have hstrip_id : ∀ (s : NNReal) (z : ℂ),
        min 0 beta ≤ z.re → z.re ≤ max 0 beta →
        (∫ x, Complex.exp (z * (x : ℂ)) ∂(P.map (X s))) =
          Complex.exp (((s : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T z) := by
      intro s
      have : IsProbabilityMeasure (P.map (X s)) :=
        Measure.isProbabilityMeasure_map (hX_meas s).aemeasurable
      let H : ℂ → ℂ := fun z =>
        (∫ x, Complex.exp (z * (x : ℂ)) ∂(P.map (X s))) -
          Complex.exp (((s : ℝ) : ℂ) * EsscherTripletWitnessProp2Aux.levyComplexExponent T z)
      have hH_cont : ContinuousOn H {z : ℂ | min 0 beta ≤ z.re ∧ z.re ≤ max 0 beta} :=
        (EsscherTripletWitnessProp2Aux.continuousOn_bilateralLaplace (hExp_integrable_map s)).sub
          ((continuousOn_const.mul
            (EsscherTripletWitnessProp2Aux.continuousOn_levyComplexExponent T hBeta)).cexp)
      have hH_diff : DifferentiableOn ℂ H {z : ℂ | min 0 beta < z.re ∧ z.re < max 0 beta} :=
        (EsscherTripletWitnessProp2Aux.differentiableOn_bilateralLaplace (hExp_integrable_map s)).sub
          (((differentiableOn_const _).mul
            (EsscherTripletWitnessProp2Aux.differentiableOn_levyComplexExponent T hBeta)).cexp)
      have hH_zero : ∀ y : ℝ, H ((y : ℂ) * I) = 0 := by
        intro y
        dsimp only [H]
        have hLHS : (∫ x, Complex.exp (((y : ℂ) * I) * (x : ℂ)) ∂(P.map (X s))) =
            charFun (P.map (X s)) y := by
          rw [charFun_apply_real]
          congr 1
          ext x
          congr 1
          ring
        have hRHS : EsscherTripletWitnessProp2Aux.levyComplexExponent T ((y : ℂ) * I) =
            Kyprianou.Ch01.levyTripleExponent T y := by
          rw [mul_comm (y : ℂ) I]
          exact EsscherTripletWitnessProp2Aux.levyComplexExponent_I_mul T y
        rw [hLHS, hRHS, hLK s y, sub_self]
      intro z hz1 hz2
      exact sub_eq_zero.mp
        (EsscherTripletWitnessProp2Aux.eq_zero_on_uIcc_strip_of_eq_zero_on_imag_axis
          hβ0 hH_cont hH_diff hH_zero z hz1 hz2)
    -- Step 4: Identify k = levyComplexExponent T beta via s = 1, z = beta
    have hk_eq : (k : ℂ) = EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ) := by
      have h1 := hstrip_id 1 (beta : ℂ) (by simp) (by simp)
      have hmap_int :
          (∫ x, Complex.exp ((beta : ℂ) * (x : ℂ)) ∂(P.map (X 1))) =
            ((∫ eta, Real.exp (beta * X 1 eta) ∂P : ℝ) : ℂ) := by
        have hcast : (fun x : ℝ => Complex.exp ((beta : ℂ) * (x : ℂ))) =
            fun x : ℝ => ((Real.exp (beta * x) : ℝ) : ℂ) := by
          ext x; rw [Complex.ofReal_exp]; push_cast; rfl
        rw [hcast,
          show (∫ x, ((Real.exp (beta * x) : ℝ) : ℂ) ∂(P.map (X 1))) =
            ((∫ x, Real.exp (beta * x) ∂(P.map (X 1)) : ℝ) : ℂ) from
              Complex.ofRealCLM.integral_comp_comm (hExp_integrable_map 1),
          integral_map (hX_meas 1).aemeasurable
            (by fun_prop : Measurable (fun x : ℝ => Real.exp (beta * x))).aestronglyMeasurable]
      rw [hmap_int] at h1
      have him : (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).im = 0 :=
        EsscherTripletWitnessProp2Aux.levyComplexExponent_ofReal_im T beta
      set r : ℝ := (EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ)).re
      have hphi_eq : EsscherTripletWitnessProp2Aux.levyComplexExponent T (beta : ℂ) = (r : ℂ) := by
        apply Complex.ext <;> simp [r, him]
      rw [hphi_eq] at h1 ⊢
      simp only [NNReal.coe_one, Complex.ofReal_one, one_mul, ← Complex.ofReal_exp] at h1
      have hreal : (∫ eta, Real.exp (beta * X 1 eta) ∂P) = Real.exp r :=
        Complex.ofReal_injective h1
      dsimp only [k]
      rw [hreal, Real.log_exp]
    -- Step 5: Evaluate at s = t, z = beta + I * xi and apply levyComplexExponent_shift
    rw [hcharFun_Q t xi,
      hstrip_id t ((beta : ℂ) + I * (xi : ℂ)) (by simp) (by simp),
      hk_eq, ← Complex.exp_add]
    congr 1
    have hshift := EsscherTripletWitnessProp2Aux.levyComplexExponent_shift
      T Tbeta hBeta hDrift hVar hLevy xi
    rw [← hshift]
    ring
