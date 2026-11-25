-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzAffineDerivativeIntervalIntegrableV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T19:45:40.383062+00:00
-- url     : https://prove2.me/submissions/8b8653c7-ee46-4140-9b35-d10072b98225

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineACV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineAEDerivativeV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The two-coordinate chain-rule integrand is interval-integrable on every
positive-coordinate affine segment of a Lipschitz path. -/
theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    IntervalIntegrable
      (fun s : ℝ => fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
        c * fderiv ℝ f (U s, a + c * s) (0, 1)) volume l r := by
  have hAC := Kyprianou.Ch04.exercise42LipschitzAffineACV1
    f hf U K hU a c l r hlr hNonneg
  have hAE := Kyprianou.Ch04.exercise42LipschitzAffineAEDerivativeV1
    f hf U K hU a c l r hPositive
  have hEq :
      (fun s : ℝ => deriv (fun u : ℝ => f (U u, a + c * u)) s) =ᵐ[
        volume.restrict (uIoc l r)]
      (fun s : ℝ => fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
        c * fderiv ℝ f (U s, a + c * s) (0, 1)) := by
    rw [uIoc_of_le hlr]
    change ∀ᵐ s ∂volume.restrict (Ioc l r),
      deriv (fun u : ℝ => f (U u, a + c * u)) s =
        fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1)
    rw [ae_restrict_iff' measurableSet_Ioc]
    exact hAE
  exact hAC.intervalIntegrable_deriv.congr_ae hEq
