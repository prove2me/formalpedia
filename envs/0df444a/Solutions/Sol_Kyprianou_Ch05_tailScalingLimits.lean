-- Prove2me | solution 1 for Kyprianou.Ch05.tailScalingLimits
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T00:49:54.534945+00:00
-- url     : https://prove2.me/submissions/bf6bd798-d65a-4d96-9e70-8f06c247b111

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
import Theorems.Thm_Kyprianou_Ch05_tailScalingFilter
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

open Kyprianou.Ch05 Set

/-- Lemma 5.17, tail scaling step: reduction to the filter-generic
`tailScalingFilter`, mirroring WillR's V2 potential-scaling proof
(`potentialScalingLimitsV2` via `potentialScalingFilter`). -/
theorem solution
    (Pi : Measure Real) (Phi L : Real → Real) (alpha : Real)
    (hAlpha1 : alpha < 1)
    (hPhi : ∀ x : Real, 0 < x → Phi (1 / x) = x ^ (-alpha) * L x) :
  ((SlowlyVaryingAtInfinity L →
     Tendsto
       (fun x : Real =>
         (Pi (Set.Ioi x)).toReal /
           (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha)))
       atTop (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           (Pi (Set.Ioi (lambda * x))).toReal / Phi (1 / x))
         atTop (nhds (lambda ^ (-alpha) / Real.Gamma (1 - alpha)))) ∧
   (SlowlyVaryingAtZero L →
     Tendsto
       (fun x : Real =>
         (Pi (Set.Ioi x)).toReal /
           (x ^ ((1 - alpha) - 1) * L x / Real.Gamma (1 - alpha)))
       (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) →
     ∀ lambda : Real, 0 < lambda →
       Tendsto
         (fun x : Real =>
           (Pi (Set.Ioi (lambda * x))).toReal / Phi (1 / x))
         (nhdsWithin (0 : Real) (Set.Ioi 0))
         (nhds (lambda ^ (-alpha) / Real.Gamma (1 - alpha))))) := by
  constructor
  · intro hslow hDens a ha
    exact tailScalingFilter Pi Phi L alpha atTop hAlpha1 (eventually_gt_atTop 0)
      hslow.1 hPhi hDens a ha (tendsto_id.const_mul_atTop ha)
      (by simpa using hslow.2 a ha)
  · intro hslow hDens a ha
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
    exact tailScalingFilter Pi Phi L alpha _ hAlpha1 he hslow.1 hPhi hDens a ha hscale
      (by simpa using hslow.2 a ha)
