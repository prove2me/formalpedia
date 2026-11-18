-- Prove2me | solution 1 for Kyprianou.Ch01.geometricIndependentCountMarksJointLaw
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T07:29:23.903914+00:00
-- url     : https://prove2.me/submissions/cf590875-0e39-4ef9-9c8f-6a60c346b459

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory
set_option autoImplicit false

/-! The count and infinite mark sequence have the exact product joint law. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (increment : ℕ → Ω → ℝ)
    (N : Ω → ℕ)
    (hNmeas : Measurable N)
    (hIncMeas : ∀ n : ℕ, Measurable (increment n))
    (hIndependent : IndepFun N
      (fun ω => fun n : ℕ => increment n ω) P) :
    P.map (fun ω => (N ω, fun n : ℕ => increment n ω)) =
      (P.map N).prod
        (P.map (fun ω => fun n : ℕ => increment n ω)) := by
  have hpath : Measurable (fun ω => fun n : ℕ => increment n ω) :=
    measurable_pi_lambda _ (fun n => hIncMeas n)
  exact hIndependent.map_prod_eq_prod_map_map
    hNmeas.aemeasurable hpath.aemeasurable
