-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaIntegralComplexExtensionV2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:51:31.922552+00:00
-- url     : https://prove2.me/submissions/3e900577-51a4-4d1e-a583-901d24fca895
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Mathlib
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaComplexDeficitValue
import Definitions.Def_Kyprianou_Ch01_RiskQueueCore
import Definitions.Def_Kyprianou_Ch01_ExplicitLevyExamples
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Complex
open scoped NNReal ENNReal
set_option autoImplicit false
universe u

theorem solution
    (alpha : ℝ) (h0 : 0 < alpha) (h1 : alpha < 1)
    (w : ℂ) (hw : w ≠ 0) (hwre : w.re ≤ 0) :
    IntegrableOn
      (fun r : ℝ =>
        (Complex.exp (w * (r : ℂ)) - 1) *
          ((r ^ (-alpha - 1) : ℝ) : ℂ))
      (Set.Ioi (0 : ℝ)) ∧
    (∫ r in Set.Ioi (0 : ℝ),
      (Complex.exp (w * (r : ℂ)) - 1) *
        (((r ^ (-alpha - 1) : ℝ)) : ℂ) ∂volume) =
      ((Real.Gamma (-alpha) : ℝ) : ℂ) *
        Complex.exp ((alpha : ℂ) * Complex.log (-w)) := by
  exact ⟨Kyprianou.Ch01.stableGammaComplexDeficitIntegrable
    alpha h0 h1 w hw hwre,
    Kyprianou.Ch01.stableGammaComplexDeficitValue
      alpha h0 h1 w hw hwre⟩
