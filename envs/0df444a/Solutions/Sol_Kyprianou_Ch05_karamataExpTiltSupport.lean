-- Prove2me | solution 1 for Kyprianou.Ch05.karamataExpTiltSupport
-- status  : ACCEPTED   (prove)
-- author  : @daga2
-- created : 2026-11-27T02:18:47.618049+00:00
-- url     : https://prove2.me/submissions/61a63899-8abe-41e3-a4df-3517b063e11a

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Exponential image of a supported tilted measure is supported on the unit interval. -/
theorem solution
    (M : Measure Real) (hs : M (Iio 0) = 0) :
    ∀ᵐ z ∂((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
      (fun z : Real => Real.exp (-z))), z ∈ Icc (0 : Real) 1 := by
  have h : ∀ᵐ z ∂M, 0 ≤ z := by
    rw [ae_iff]
    simpa only [not_le] using (show M {z : Real | z < 0} = 0 from hs)
  have hφ : Measurable (fun z : Real => Real.exp (-z)) := by fun_prop
  have h' : ∀ᵐ z ∂(M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))),
      0 ≤ z := (withDensity_absolutelyContinuous M _).ae_le h
  change ∀ᵐ z ∂((M.withDensity (fun z : Real => ENNReal.ofReal (Real.exp (-z)))).map
    (fun z : Real => Real.exp (-z))), 0 ≤ z ∧ z ≤ 1
  -- FIX (WillR 99537f33 CE line 20): `ae_map_iff` takes an `AEMeasurable`
  -- argument, not a `Measurable` one; use `hφ.aemeasurable`.
  rw [ae_map_iff hφ.aemeasurable
    (measurableSet_Icc : MeasurableSet (Icc (0 : Real) 1))]
  filter_upwards [h'] with z hz
  exact ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz)⟩
