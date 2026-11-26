-- Prove2me | solution 1 for Kyprianou.Ch05.karamataDilationSupportMass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T21:44:42.477965+00:00
-- url     : https://prove2.me/submissions/f86f101a-d8d4-410f-8979-8305f31dae12

import Mathlib
import Definitions.Def_Kyprianou_Ch05_RegularVariation
import Definitions.Def_Kyprianou_Ch05_MonotoneDensity
open MeasureTheory Filter Set
open scoped NNReal ENNReal
set_option autoImplicit false
open Kyprianou.Ch05

/-- Positive dilation preserves support and transports mass of the unit interval. -/
theorem solution
    (U : Measure Real) (x c : Real) (hx : 0 < x)
    (hs : U (Iio 0) = 0) :
    let M := (ENNReal.ofReal c) • (Measure.map (fun z : Real => z/x) U)
    M (Iio 0) = 0 ∧ M (Icc 0 1) = ENNReal.ofReal c * U (Icc 0 x) := by
  dsimp only
  have hm : Measurable (fun z : Real => z/x) := by fun_prop
  have hneg : (fun z : Real => z/x) ⁻¹' Iio 0 = Iio 0 := by
    ext z
    change z/x < 0 ↔ z < 0
    rw [div_lt_iff₀ hx,zero_mul]
  have hunit : (fun z : Real => z/x) ⁻¹' Icc 0 1 = Icc 0 x := by
    ext z
    change (0 ≤ z/x ∧ z/x ≤ 1) ↔ (0 ≤ z ∧ z ≤ x)
    rw [le_div_iff₀ hx,div_le_iff₀ hx,zero_mul,one_mul]
  constructor
  · rw [Measure.smul_apply,Measure.map_apply hm measurableSet_Iio,hneg,hs]
    simp
  · rw [Measure.smul_apply,Measure.map_apply hm measurableSet_Icc,hunit]
    rfl
