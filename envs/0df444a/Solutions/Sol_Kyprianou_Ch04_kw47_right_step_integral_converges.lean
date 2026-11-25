-- Prove2me | solution 1 for Kyprianou.Ch04.kw47_right_step_integral_converges
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T12:15:54.707008+00:00
-- url     : https://prove2.me/submissions/a7ee6b81-86ae-469e-acf2-7acc76af5c05

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (mu : Measure Real) [IsFiniteMeasure mu]
    (f : Real → Real) (B : Real) (r : Nat → Real → Real)
    (hf : Measurable f) (hr : ∀ n, Measurable (r n))
    (hbound : ∀ x, ‖f x‖ ≤ B)
    (hlim : ∀ᵐ x ∂mu, Tendsto (fun n => r n x) atTop (nhdsWithin x (Ici x)))
    (hRight : ∀ x, ContinuousWithinAt f (Ici x) x) :
    Tendsto (fun n => ∫ x, f (r n x) ∂mu) atTop (nhds (∫ x, f x ∂mu))  := by
  apply tendsto_integral_of_dominated_convergence (fun _ => B)
    (fun n => (hf.comp (hr n)).aestronglyMeasurable) (integrable_const B)
    (fun n => Eventually.of_forall fun x => hbound (r n x))
  filter_upwards [hlim] with x hx
  exact (hRight x).tendsto.comp hx
