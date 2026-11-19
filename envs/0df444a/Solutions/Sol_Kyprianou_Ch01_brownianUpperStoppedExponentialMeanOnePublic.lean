-- Prove2me | solution 1 for Kyprianou.Ch01.brownianUpperStoppedExponentialMeanOnePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T09:27:27.563194+00:00
-- url     : https://prove2.me/submissions/bcf14c3a-defe-463b-b759-93dd8a172966

import Mathlib.Topology.Separation.Hausdorff
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperBoundedStoppedExponentialMeanOnePublic
import Theorems.Thm_Kyprianou_Ch01_brownianUpperStoppedExponentialMeanLimitPublic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The bounded stopping and infinite-horizon limit identities imply the upper passage stopped mean. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → ℝ)
    (sigma gamma q x : ℝ)
    (hsigma : 0 < sigma) (hq : 0 < q) (hx : 0 < x)
    (hX : IsLinearBrownian P X sigma gamma)
    (hMeas : ∀ t : ℝ≥0, Measurable (X t)) :
    let theta : ℝ :=
      (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
    Integrable (passageLaplace (firstUpperPassage X x) q) P ∧
    (∫ ω, Real.exp (theta * x) *
      passageLaplace (firstUpperPassage X x) q ω ∂P) = 1 := by
  let theta : ℝ :=
    (Real.sqrt (gamma ^ 2 + 2 * sigma ^ 2 * q) - gamma) / sigma ^ 2
  let F : ℕ → Ω → ℝ := fun N ω =>
    let T : ℝ≥0 := N
    let tauT : ℝ≥0 :=
      match firstUpperPassage X x ω with
      | none => T
      | some t => min t T
    Real.exp (theta * X tauT ω - q * (tauT : ℝ))
  obtain ⟨hInt, hlimit⟩ :=
    brownianUpperStoppedExponentialMeanLimitPublic
      P X sigma gamma q x hsigma hq hx hX hMeas
  have hmean (N : ℕ) : (∫ ω, F N ω ∂P) = 1 :=
    (brownianUpperBoundedStoppedExponentialMeanOnePublic
      P X sigma gamma q x hsigma hq hx hX hMeas (N : ℝ≥0)).2
  have hconst : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1) :=
    tendsto_const_nhds
  have hlim1 : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (nhds (Real.exp (theta * x) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P))) :=
    hlimit.congr' (Filter.Eventually.of_forall hmean)
  have heq : Real.exp (theta * x) *
      (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) = 1 :=
    tendsto_nhds_unique hlim1 hconst
  refine ⟨hInt, ?_⟩
  calc
    (∫ ω, Real.exp (theta * x) *
      passageLaplace (firstUpperPassage X x) q ω ∂P) =
      Real.exp (theta * x) *
        (∫ ω, passageLaplace (firstUpperPassage X x) q ω ∂P) := by
          rw [integral_const_mul]
    _ = 1 := heq
