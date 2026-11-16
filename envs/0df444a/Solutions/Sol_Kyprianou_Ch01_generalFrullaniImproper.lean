-- Prove2me | solution 1 for Kyprianou.Ch01.generalFrullaniImproper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T10:38:16.111679+00:00
-- url     : https://prove2.me/submissions/2812f4c5-7da9-463b-975d-db22aec07f3f

import Mathlib
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Real
open scoped Topology
set_option autoImplicit false

/-- The two-ended Frullani limit specialised to reciprocal endpoints. -/
theorem solution
    (f f' : ℝ → ℝ) (fInfinity : ℝ)
    (hfderiv : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (hfprime : Continuous f')
    (hlimit : Tendsto f atTop (nhds fInfinity))
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun R : ℝ =>
        ∫ x in (1 / R)..R,
          (f (a * x) - f (b * x)) / x)
      atTop
      (nhds ((f 0 - fInfinity) * Real.log (b / a))) := by
  have hcont : Continuous f :=
    continuous_iff_continuousAt.mpr (fun x => (hfderiv x).continuousAt)
  have hloc : LocallyIntegrableOn f (Set.Ioi 0) volume :=
    hcont.continuousOn.locallyIntegrableOn measurableSet_Ioi
  have hzero : Tendsto f (nhdsWithin 0 (Set.Ioi 0)) (nhds (f 0)) :=
    hcont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hpair : Tendsto
      (fun R : ℝ => ((R⁻¹ : ℝ), R))
      atTop ((nhdsWithin 0 (Set.Ioi 0)) ×ˢ atTop) :=
    tendsto_inv_atTop_nhdsGT_zero.prodMk tendsto_id
  have h := (Frullani.tendsto_intervalIntegral hloc ha
    (lt_trans ha hab) hzero hlimit).comp hpair
  simpa only [Function.comp_def, one_div, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_one] using h
