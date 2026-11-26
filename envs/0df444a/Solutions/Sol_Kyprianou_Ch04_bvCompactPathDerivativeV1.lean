-- Prove2me | solution 1 for Kyprianou.Ch04.bvCompactPathDerivativeV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:45:10.236189+00:00
-- url     : https://prove2.me/submissions/48e88b1a-7e0e-46ae-8be4-f5a73c7eb0a0

import Mathlib
import Theorems.Thm_Kyprianou_Ch04_signedAtomicCumulativeDerivativeV1
import Theorems.Thm_Kyprianou_Ch04_tsumJumpHorizonRestrictV1
open MeasureTheory Set Filter Topology Function
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A drift plus an absolutely summable compact jump representation has derivative d a.e. -/
theorem solution (x : ℝ≥0 → ℝ) (d : ℝ)
    (hrep : ∀ t : ℝ≥0,
      Summable (fun s : Ioc (0 : ℝ≥0) t => |x s - leftLim x s|) ∧
      x t = d * (t : ℝ) + ∑' s : Ioc (0 : ℝ≥0) t, (x s - leftLim x s)) :
    ∀ᵐ s : ℝ ∂volume.restrict (Ioo (0 : ℝ) 1),
      HasDerivAt (fun t : ℝ => x (Real.toNNReal t)) d s := by
  let j : ℝ≥0 → ℝ := fun t => x t - leftLim x t
  let a : Ioc (0 : ℝ≥0) 1 → ℝ := fun t => ((t : ℝ≥0) : ℝ)
  let w : Ioc (0 : ℝ≥0) 1 → ℝ := fun t => j t
  let J : ℝ → ℝ := fun t => ∑' i, (a ⁻¹' Iic t).indicator w i
  let F : ℝ → ℝ := fun t => d * t + J t
  have hF (t : ℝ≥0) (ht : t ≤ 1) : F (t : ℝ) = x t := by
    have h := Kyprianou.Ch04.tsumJumpHorizonRestrictV1 j t 1 ht
    change _ = J (t : ℝ) at h
    rw [(hrep t).2]
    change d * (t : ℝ) + J (t : ℝ) = d * (t : ℝ) + ∑' s : Ioc (0 : ℝ≥0) t, j s
    rw [h]
  have hJ := Kyprianou.Ch04.signedAtomicCumulativeDerivativeV1 a w (hrep 1).1
  filter_upwards [ae_restrict_of_ae hJ, ae_restrict_mem measurableSet_Ioo] with s hs hm
  have hdF : HasDerivAt F d s := by
    change HasDerivAt ((fun t : ℝ => d * t) + J) d s
    simpa only [id_eq, mul_one, add_zero] using ((hasDerivAt_id s).const_mul d).add hs
  have hE : F =ᶠ[nhds s] (fun t : ℝ => x (Real.toNNReal t)) := by
    filter_upwards [Ioo_mem_nhds hm.1 hm.2] with t ht
    have hco : ((Real.toNNReal t : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.1.le
    have hle : Real.toNNReal t ≤ 1 := by
      exact_mod_cast (show ((Real.toNNReal t : ℝ≥0) : ℝ) ≤ 1 by rw [hco]; exact ht.2.le)
    simpa only [hco] using hF (Real.toNNReal t) hle
  exact hdF.congr_of_eventuallyEq hE.symm
