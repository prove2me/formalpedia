-- Prove2me | solution 1 for Kyprianou.Ch01.eLpNormIndicatorOneLeTwoByMeasurePublic
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:16:41.859308+00:00
-- url     : https://prove2.me/submissions/4ae6ff79-2f36-4ea3-9e1b-bc4bc8091b82

import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.Tactic.NormNum
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal NNReal
set_option autoImplicit false

/-- Hölder's inequality on the restricted event in the L1/L2 form. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P)
    (s : Set Ω) (hs : MeasurableSet s) :
    eLpNorm (s.indicator f) 1 P ≤
      eLpNorm f 2 P * (P s) ^ (1 / 2 : ℝ) := by
  rw [eLpNorm_indicator_eq_eLpNorm_restrict hs]
  have hLP : eLpNorm f 1 (P.restrict s) ≤
      eLpNorm f 2 (P.restrict s) *
        (P.restrict s Set.univ) ^
          (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
    eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hf.restrict
  have hComp : eLpNorm f 2 (P.restrict s) ≤ eLpNorm f 2 P :=
    eLpNorm_restrict_le f 2 P s
  calc
    eLpNorm f 1 (P.restrict s) ≤
      eLpNorm f 2 (P.restrict s) *
        (P.restrict s Set.univ) ^
          (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) := hLP
    _ ≤ eLpNorm f 2 P *
        (P.restrict s Set.univ) ^
          (1 / (1 : ENNReal).toReal - 1 / (2 : ENNReal).toReal) :=
      by gcongr <;> exact hComp
    _ = eLpNorm f 2 P * (P s) ^ (1 / 2 : ℝ) := by
      simp [Measure.restrict_apply' hs] <;> norm_num

