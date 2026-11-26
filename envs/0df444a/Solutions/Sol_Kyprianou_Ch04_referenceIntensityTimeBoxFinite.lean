-- Prove2me | solution 1 for Kyprianou.Ch04.referenceIntensityTimeBoxFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:35:51.886183+00:00
-- url     : https://prove2.me/submissions/3fbb770c-da90-443e-9ac5-c738edeb5527

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory LevyStochCalc.Poisson
open scoped ENNReal NNReal
set_option autoImplicit false
universe u

/-- Finite mark intensity implies finite intensity of a bounded positive-time box. -/
theorem solution
    {E : Type u} [MeasurableSpace E] (ν : Measure E) [SigmaFinite ν]
    (a b : NNReal) (A : Set E) (hA : ν A ≠ ⊤) :
    referenceIntensity ν (Set.Ioc (a : ℝ) (b : ℝ) ×ˢ A) ≠ ⊤ := by
  rw [referenceIntensity, Measure.prod_prod, Measure.restrict_apply measurableSet_Ioc]
  have heq : Set.Ioc (a : ℝ) (b : ℝ) ∩ Set.Ici (0 : ℝ) =
      Set.Ioc (a : ℝ) (b : ℝ) :=
    Set.inter_eq_left.mpr (fun _ hz => (NNReal.coe_nonneg a).trans hz.1.le)
  rw [heq, Real.volume_Ioc]
  exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hA
