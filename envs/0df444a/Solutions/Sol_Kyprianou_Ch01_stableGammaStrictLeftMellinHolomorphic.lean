-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaStrictLeftMellinHolomorphic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T15:37:53.04511+00:00
-- url     : https://prove2.me/submissions/4426dba9-0803-40c7-b43d-d986aea2ca28

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDensityComplexMGF
import Theorems.Thm_Kyprianou_Ch01_stableGammaStrictLeftDensityNegativeLaplaceIntegrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Complex Real Set Filter ProbabilityTheory Kyprianou.Ch01
set_option autoImplicit false

/-- Holomorphy of the Mellin integral via the complex moment generating function. -/
theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1) :
    AnalyticOnNhd ℂ (fun w : ℂ =>
      ∫ r in Set.Ioi (0 : ℝ),
        Complex.exp (w * (r : ℂ)) *
          ((r ^ (-alpha) : ℝ) : ℂ) ∂volume)
      {w : ℂ | w.re < 0} := by
  let mu : Measure ℝ :=
    (volume.restrict (Set.Ioi (0 : ℝ))).withDensity
      (fun r : ℝ => ENNReal.ofReal (r ^ (-alpha)))
  have hdom :
      Set.Iio (0 : ℝ) ⊆
        ProbabilityTheory.integrableExpSet (fun r : ℝ => r) mu := by
    intro t ht
    exact Kyprianou.Ch01.stableGammaStrictLeftDensityNegativeLaplaceIntegrable
      alpha h0 h1 t ht
  have hinside :
      Set.Iio (0 : ℝ) ⊆
        interior (ProbabilityTheory.integrableExpSet (fun r : ℝ => r) mu) :=
    interior_maximal hdom isOpen_Iio
  have hfunc :
      (fun w : ℂ =>
        ∫ r in Set.Ioi (0 : ℝ),
          Complex.exp (w * (r : ℂ)) *
            ((r ^ (-alpha) : ℝ) : ℂ) ∂volume) =
      ProbabilityTheory.complexMGF (fun r : ℝ => r) mu := by
    funext w
    exact (Kyprianou.Ch01.stableGammaStrictLeftDensityComplexMGF alpha w).symm
  rw [hfunc]
  intro w hw
  exact ProbabilityTheory.analyticAt_complexMGF
    (hinside (show w.re < 0 from hw))
