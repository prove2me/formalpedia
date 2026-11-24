-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentNegativeTailWeightedV1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:30:57.087811+00:00
-- url     : https://prove2.me/submissions/124fca00-3ff6-427a-a214-8e141e2a7a5a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_Kyprianou_Ch03_stableFracMomentNegativeTailWeightEqV1
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha cPlus cMinus eta : Real) (hCPlus : 0 ≤ cPlus)
    (hCMinus : 0 ≤ cMinus) (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) (Set.Iic (-1 : Real))
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔
    IntegrableOn (fun x : Real => cMinus * (-x) ^ (eta - 1 - alpha))
      (Set.Iic (-1 : Real)) volume := by
  let D (x : ℝ) : ℝ := if 0 < x then cPlus / (x ^ (1 + alpha))
    else if x < 0 then cMinus / ((-x) ^ (1 + alpha)) else 0
  let w (x : ℝ) : ℝ≥0 := (D x).toNNReal
  have hD : Measurable D := by
    dsimp [D]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
      (by fun_prop) (Measurable.ite (measurableSet_lt measurable_id measurable_const)
        (by fun_prop) measurable_const)
  have hw : Measurable w := hD.real_toNNReal
  change Integrable (fun x : ℝ => (max |x| 1)^eta)
    ((volume.withDensity (fun x => (w x : ENNReal))).restrict (Iic (-1 : ℝ))) ↔ _
  rw [restrict_withDensity measurableSet_Iic, integrable_withDensity_iff_integrable_smul hw]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Iic] with x hx
  change x ≤ -1 at hx
  exact Kyprianou.Ch03.stableFracMomentNegativeTailWeightEqV1 alpha cPlus cMinus eta x hCMinus hx
