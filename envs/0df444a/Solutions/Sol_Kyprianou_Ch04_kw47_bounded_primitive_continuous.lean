-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_bounded_primitive_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T16:04:01.193375+00:00
-- url     : https://prove2.me/submissions/feb0138e-af2f-4190-9bb4-09b542453361

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (f : Real → Real) (hf : Measurable f) (h : ∀ x, ‖f x‖ ≤ 1) :
    Continuous (fun t : NNReal => ∫ s in Icc (0 : Real) (t : Real), f s ∂volume) := by 
  have hi (a b : Real) : IntervalIntegrable f volume a b := by
    rw [intervalIntegrable_iff']
    have h1 : IntegrableOn (fun _ : Real => (1 : Real)) (uIcc a b) volume :=
      integrableOn_const (by simp [uIcc])
    exact h1.mono' hf.aestronglyMeasurable
      (Eventually.of_forall h)
  have hc := (intervalIntegral.continuous_primitive hi 0).comp
    (continuous_subtype_val : Continuous (fun t : NNReal => (t : Real)))
  have heq : (fun t : NNReal => ∫ s in Icc (0 : Real) (t : Real), f s ∂volume) =
      (fun t : NNReal => ∫ s in (0 : Real)..(t : Real), f s ∂volume) := by
    funext t
    calc
      (∫ s in Icc (0 : Real) (t : Real), f s ∂volume) =
          ∫ s in Ioc (0 : Real) (t : Real), f s ∂volume := integral_Icc_eq_integral_Ioc
      _ = ∫ s in (0 : Real)..(t : Real), f s ∂volume :=
        (intervalIntegral.integral_of_le (show (0 : Real) ≤ (t : Real) from t.property)).symm
  rw [heq]
  exact hc
