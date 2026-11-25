-- Prove2me | solution 1 for Kyprianou.Ch04.exercise42LipschitzAffineSegmentChainV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T18:39:10.353507+00:00
-- url     : https://prove2.me/submissions/8df10ec4-bbd2-4b95-b9cf-7822baa8c3ff

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineACV1
import Theorems.Thm_Kyprianou_Ch04_exercise42LipschitzAffineAEDerivativeV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ × ℝ → ℝ)
    (hf : ContDiffOn ℝ 1 f (Set.prod (Set.Ici (0 : ℝ)) Set.univ))
    (U : ℝ → ℝ) (K : ℝ≥0) (hU : LipschitzWith K U)
    (a c l r : ℝ) (hlr : l ≤ r)
    (hNonneg : ∀ s ∈ Icc l r, 0 ≤ U s)
    (hPositive : ∀ s ∈ Ioc l r, 0 < U s) :
    f (U r, a + c * r) - f (U l, a + c * l) =
      ∫ s in l..r, fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
        c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
  have hAC := Kyprianou.Ch04.exercise42LipschitzAffineACV1
    f hf U K hU a c l r hlr hNonneg
  have hder := Kyprianou.Ch04.exercise42LipschitzAffineAEDerivativeV1
    f hf U K hU a c l r hPositive
  have hReverse : ∀ᵐ s ∂volume, s ∈ Ioc r l →
      deriv (fun u : ℝ => f (U u, a + c * u)) s =
        fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1) := by
    filter_upwards with s hs
    exact (not_lt_of_ge hlr (lt_of_lt_of_le hs.1 hs.2)).elim
  have hi := intervalIntegral.integral_congr_ae' hder hReverse
  calc
    f (U r, a + c * r) - f (U l, a + c * l) =
        ∫ s in l..r, deriv (fun u : ℝ => f (U u, a + c * u)) s := by
          simpa only [Function.comp_def] using hAC.integral_deriv_eq_sub.symm
    _ = ∫ s in l..r,
        fderiv ℝ f (U s, a + c * s) (1, 0) * deriv U s +
          c * fderiv ℝ f (U s, a + c * s) (0, 1) := hi
