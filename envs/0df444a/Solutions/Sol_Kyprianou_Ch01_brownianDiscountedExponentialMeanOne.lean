-- Prove2me | solution 1 for Kyprianou.Ch01.brownianDiscountedExponentialMeanOne
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-15T21:23:59.20111+00:00
-- url     : https://prove2.me/submissions/cc865208-082a-4170-a470-c8d791b95b6d

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
open MeasureTheory ProbabilityTheory Kyprianou.Ch01
open scoped NNReal ENNReal
set_option autoImplicit false

theorem KypBDEM_root
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q := by
  intro theta
  have hs2 : 0 < sigma ^ 2 := by positivity
  have hnn : 0 ≤ gamma ^ 2 + 2 * sigma ^ 2 * q := by positivity
  set s := Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) with hs
  have hsq : s ^ 2 = gamma ^ 2 + 2 * sigma ^ 2 * q := Real.sq_sqrt hnn
  show sigma ^ 2 * ((s - gamma) / sigma ^ 2) ^ 2 / 2 + gamma * ((s - gamma) / sigma ^ 2) = q
  field_simp
  nlinarith [hsq]

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q : ℝ) (hsigma : 0 < sigma) (hq : 0 < q)
    (hX : Kyprianou.Ch01.IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) (t : ℝ≥0) :
    let theta := (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    Integrable (fun ω => Real.exp (theta * X t ω - q * (t : ℝ))) P ∧
    (∫ ω, Real.exp (theta * X t ω - q * (t : ℝ)) ∂P) = 1 := by
  intro theta
  have hroot := KypBDEM_root sigma gamma q hsigma hq
  have hv : 0 ≤ sigma ^ 2 * (t : ℝ) := by positivity
  set v : ℝ≥0 := (⟨sigma ^ 2 * t, hv⟩ : ℝ≥0) with hvdef
  have hvc : (v : ℝ) = sigma ^ 2 * t := rfl
  have hlaw : P.map (X t) = gaussianReal (gamma * t) v := by
    have : IsProbabilityMeasure (P.map (X t)) :=
      Measure.isProbabilityMeasure_map (hMeas t).aemeasurable
    have : IsProbabilityMeasure (gaussianReal (gamma * t) v) :=
      instIsProbabilityMeasureGaussianReal _ _
    apply Measure.ext_of_charFun
    funext ξ
    rw [hX.2.2 t ξ, charFun_gaussianReal]
    congr 1
    rw [hvc]
    push_cast
    ring
  have hexp : ∀ ω, Real.exp (theta * X t ω - q * (t : ℝ))
      = Real.exp (-(q * (t : ℝ))) * Real.exp (theta * X t ω) := by
    intro ω; rw [← Real.exp_add]; ring_nf
  have hint0 : Integrable (fun ω => Real.exp (theta * X t ω)) P := by
    have h := integrable_exp_mul_gaussianReal (μ := gamma * t)
      (v := v) theta
    rw [← hlaw] at h
    exact (integrable_map_measure (by
      exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).aestronglyMeasurable)
      (hMeas t).aemeasurable).mp h
  refine ⟨?_, ?_⟩
  · simp_rw [hexp]
    exact hint0.const_mul _
  · simp_rw [hexp]
    rw [integral_const_mul]
    have hm := mgf_gaussianReal hlaw theta
    unfold mgf at hm
    rw [hm, ← Real.exp_add]
    rw [← Real.exp_zero]
    congr 1
    show _ = (0:ℝ)
    rw [hvc]
    have : sigma ^ 2 * theta ^ 2 / 2 + gamma * theta = q := hroot
    linear_combination (t : ℝ) * this
