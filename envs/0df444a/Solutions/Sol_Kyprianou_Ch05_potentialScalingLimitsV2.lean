-- Prove2me | solution 1 for Kyprianou.Ch05.potentialScalingLimitsV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:38:42.992815+00:00
-- url     : https://prove2.me/submissions/2e991c84-49b7-4d53-b5f6-46ee8e380576

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_potentialScalingFilter
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- Corrected reciprocal-factor proof. -/
theorem solution
    (U : Measure Real) (Phi L : Real → Real) (rho : Real)
    (hRho : 0 ≤ rho)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-rho) / L x) :
  ((SlowlyVaryingAtInfinity L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       atTop (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         atTop (nhds (lambda ^ rho / Real.Gamma (1 + rho)))) ∧
   (SlowlyVaryingAtZero L →
     Tendsto
       (fun x : Real =>
         ((U) (Set.Icc (0 : Real) x)).toReal /
           (x ^ rho * L x / Real.Gamma (1 + rho)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           ((U) (Set.Icc (0 : Real) (lambda * x))).toReal * Phi (1 / x))
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (lambda ^ rho / Real.Gamma (1 + rho))))) := by
  constructor
  · intro hslow hCum a ha
    exact potentialScalingFilter U Phi L rho atTop hRho (eventually_gt_atTop 0)
      hslow.1 hPhi hCum a ha (tendsto_id.const_mul_atTop ha)
      (by simpa using hslow.2 a ha)
  · intro hslow hCum a ha
    have he : ∀ᶠ x : Real in nhdsWithin (0 : Real) (Set.Ioi 0), 0 < x :=
      self_mem_nhdsWithin
    have hscale : Tendsto (fun x : Real => a*x) (nhdsWithin (0 : Real) (Set.Ioi 0))
        (nhdsWithin (0 : Real) (Set.Ioi 0)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_,?_⟩
      · have hi : Tendsto (fun x : Real => x) (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        simpa only [mul_zero] using hi.const_mul a
      · filter_upwards [he] with x hx
        exact mul_pos ha hx
    exact potentialScalingFilter U Phi L rho _ hRho he hslow.1 hPhi hCum a ha hscale
      (by simpa using hslow.2 a ha)
