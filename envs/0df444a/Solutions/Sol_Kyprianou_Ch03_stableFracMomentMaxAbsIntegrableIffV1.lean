-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentMaxAbsIntegrableIffV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T15:47:02.359829+00:00
-- url     : https://prove2.me/submissions/06850ef0-740a-4eca-9dbd-de18698a9cd8

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_IsSubmultiplicative
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Y : Omega → Real) (hY : AEMeasurable Y P) (eta : Real) (heta : 0 < eta) :
    Integrable (fun w => |Y w| ^ eta) P ↔
      Integrable (fun w => (max |Y w| 1) ^ eta) P := by
  let f (x : ℝ) := |x| ^ eta
  let g (x : ℝ) := (max |x| 1) ^ eta
  have hf : Measurable f := by dsimp [f]; fun_prop
  have hg : Measurable g := by dsimp [g]; fun_prop
  have ha (x : ℝ) : 0 ≤ f x := Real.rpow_nonneg (abs_nonneg _) _
  have hb (x : ℝ) : 0 ≤ g x := Real.rpow_nonneg (le_trans (abs_nonneg _) (le_max_left _ _)) _
  have hfg (x : ℝ) : f x ≤ g x := Real.rpow_le_rpow (abs_nonneg _) (le_max_left _ _) heta.le
  have hgf (x : ℝ) : g x ≤ 1 + f x := by
    by_cases h : |x| ≤ 1
    · dsimp [g]; rw [max_eq_right h, Real.one_rpow]
      linarith [ha x]
    · dsimp [g]; rw [max_eq_left (le_of_lt (lt_of_not_ge h))]
      change f x ≤ 1 + f x
      linarith
  constructor
  · intro h
    apply ((integrable_const (1 : ℝ)).add h).mono (hg.comp_aemeasurable hY).aestronglyMeasurable
    filter_upwards [] with w
    change ‖g (Y w)‖ ≤ ‖1 + f (Y w)‖
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hb _),
      abs_of_nonneg (show 0 ≤ 1 + f (Y w) by linarith [ha (Y w)])] using hgf (Y w)
  · intro h
    apply h.mono (hf.comp_aemeasurable hY).aestronglyMeasurable
    filter_upwards [] with w
    change ‖f (Y w)‖ ≤ ‖g (Y w)‖
    simpa only [Real.norm_eq_abs, abs_of_nonneg (ha _), abs_of_nonneg (hb _)] using hfg (Y w)
