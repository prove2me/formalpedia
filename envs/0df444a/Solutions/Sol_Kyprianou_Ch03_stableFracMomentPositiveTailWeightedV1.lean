-- Prove2me | solution 1 for Kyprianou.Ch03.stableFracMomentPositiveTailWeightedV1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-24T16:03:58.682716+00:00
-- url     : https://prove2.me/submissions/f02889aa-9ea8-4008-86fe-316b9a5352c0

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false
theorem solution
    (alpha cPlus cMinus eta : Real) (hCPlus : 0 ≤ cPlus)
    (hCMinus : 0 ≤ cMinus) (hEta : 0 < eta) :
    IntegrableOn (fun x : Real => (max |x| 1) ^ eta) (Set.Ici (1 : Real))
      ((volume : Measure Real).withDensity
        (fun x : Real => ENNReal.ofReal
          (if 0 < x then cPlus / (x ^ (1 + alpha))
           else if x < 0 then cMinus / ((-x) ^ (1 + alpha))
           else 0))) ↔
    IntegrableOn (fun x : Real => cPlus * x ^ (eta - 1 - alpha))
      (Set.Ici (1 : Real)) volume := by
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
    ((volume.withDensity (fun x => (w x : ENNReal))).restrict (Ici (1 : ℝ))) ↔ _
  rw [restrict_withDensity measurableSet_Ici, integrable_withDensity_iff_integrable_smul hw]
  apply integrable_congr
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  change 1 ≤ x at hx
  have hp : 0 < x := by linarith
  have h1 : 1 ≤ x := by linarith
  have hd : D x = cPlus / (x ^ (1+alpha)) := by
    dsimp [D]
    rw [if_pos hp]
  have hn : 0 ≤ D x := by rw [hd]; positivity
  change ((w x : ℝ) * (max |x| 1)^eta) = _
  rw [show (w x : ℝ) = D x by simp [w, Real.coe_toNNReal, hn], hd]
  rw [abs_of_pos hp, max_eq_left h1]
  calc
    _ = cPlus * (x ^ eta / x ^ (1+alpha)) := by ring
    _ = _ := by rw [← Real.rpow_sub hp]; congr 2 <;> ring
