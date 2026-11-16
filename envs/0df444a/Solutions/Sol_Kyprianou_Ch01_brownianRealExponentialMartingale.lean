-- Prove2me | solution 1 for Kyprianou.Ch01.brownianRealExponentialMartingale
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T14:47:03.987109+00:00
-- url     : https://prove2.me/submissions/787b7708-7c1f-4ef4-8a6e-20262a07cbfa

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Theorems.Thm_Kyprianou_Ch01_brownianRealExpMoment
import Theorems.Thm_Kyprianou_Ch01_brownianRealExpPastFactorisation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Normalise the Brownian exponential using its MGF and increment factorisation. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma theta : ℝ)
    (hsigma : 0 < sigma)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
    let M : ℝ≥0 → Ω → ℝ :=
      fun t ω => Real.exp (theta * X t ω - psi * (t : ℝ))
    ∀ (s t : ℝ≥0), s ≤ t →
      Integrable (M t) P ∧
      ∀ A : Set Ω,
        @MeasurableSet Ω (naturalSigma X s) A →
        (∫ ω in A, M t ω ∂P) = (∫ ω in A, M s ω ∂P) := by
  dsimp only
  intro s t hst
  let psi : ℝ := sigma ^ 2 * theta ^ 2 / 2 + gamma * theta
  let M : ℝ≥0 → Ω → ℝ :=
    fun r ω => Real.exp (theta * X r ω - psi * (r : ℝ))
  have hm (r : ℝ≥0) :=
    Kyprianou.Ch01.brownianRealExpMoment P X sigma gamma theta
      hsigma hX hMeas r
  have he (r : ℝ≥0) (ω : Ω) :
      M r ω = Real.exp (-(psi * (r : ℝ))) * Real.exp (theta * X r ω) := by
    dsimp [M]
    rw [← Real.exp_add]
    congr 1
    ring
  have ht : Integrable (M t) P := by
    have hh := (hm t).1.const_mul (Real.exp (-(psi * (t : ℝ))))
    convert hh using 1
    funext ω
    exact he t ω
  refine ⟨ht, ?_⟩
  intro A hA
  have hfactor :=
    Kyprianou.Ch01.brownianRealExpPastFactorisation P X sigma gamma theta
      hsigma hX hMeas s t hst A hA
  have hsub : ((t - s : ℝ≥0) : ℝ) = (t : ℝ) - (s : ℝ) := by
    exact_mod_cast NNReal.coe_sub hst
  have hexp :
      Real.exp (-(psi * (t : ℝ))) *
        Real.exp (psi * ((t - s : ℝ≥0) : ℝ)) =
          Real.exp (-(psi * (s : ℝ))) := by
    rw [← Real.exp_add, hsub]
    congr 1
    ring
  have hid (r : ℝ≥0) :
      (∫ ω in A, M r ω ∂P) =
        Real.exp (-(psi * (r : ℝ))) *
          (∫ ω in A, Real.exp (theta * X r ω) ∂P) := by
    simp only [he, integral_const_mul]
  rw [hid t, hfactor, (hm (t - s)).2]
  rw [← mul_assoc, hexp, ← hid s]
