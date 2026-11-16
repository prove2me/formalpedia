-- Prove2me | solution 1 for Kyprianou.Ch01.stableGammaDeficitIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T21:34:04.855984+00:00
-- url     : https://prove2.me/submissions/b26d0999-976b-4041-9ba5-fda50d665b67

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Theorems.Thm_Kyprianou_Ch01_stableGammaPowerEnvelopeIntegrable
import Theorems.Thm_Kyprianou_Ch01_stableGammaDeficitEnvelopeBound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Real Set
set_option autoImplicit false

/-- Absolute integrability from the explicit positive power envelope. -/
theorem solution
    (alpha u : ℝ) (ha0 : 0 < alpha) (ha1 : alpha < 1) (hu : 0 < u) :
    IntegrableOn (fun x : ℝ =>
      (Real.exp (-(u * x)) - 1) * x ^ (-alpha - 1))
      (Set.Ioi (0 : ℝ)) := by
  have henv :=
    Kyprianou.Ch01.stableGammaPowerEnvelopeIntegrable
      alpha u ha0 ha1 hu
  apply Integrable.mono' henv
  · fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact Kyprianou.Ch01.stableGammaDeficitEnvelopeBound
      alpha u ha0 ha1 hu x hx
