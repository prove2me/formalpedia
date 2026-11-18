-- Prove2me | solution 1 for Kyprianou.Ch01.stableAlphaOneCosinePositiveIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T08:38:46.147964+00:00
-- url     : https://prove2.me/submissions/ffe31156-5b62-47db-a240-cf623bf5e1fb

import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineTailIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableAlphaOneCosineNearZeroIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Real
set_option autoImplicit false
/-! Integrability on the entire positive half line by measurable interval union. -/
theorem solution :
    IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
    (Set.Ioi (0 : ℝ)) := by
  have hNear :
      IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
        (Ioc (0 : ℝ) 1) :=
    (integrableOn_Ioc_iff_integrableOn_Ioo).2
      Kyprianou.Ch01.stableAlphaOneCosineNearZeroIntegrable
  have hTail :
      IntegrableOn (fun r : ℝ => (1 - Real.cos r) / r ^ 2)
        (Ioi (1 : ℝ)) :=
    Kyprianou.Ch01.stableAlphaOneCosineTailIntegrable
  have hunion := hNear.union hTail
  simpa only [Ioc_union_Ioi_eq_Ioi (by norm_num : (0 : ℝ) ≤ 1)] using hunion
