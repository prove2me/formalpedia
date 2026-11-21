-- Prove2me | solution 1 for Kyprianou.Ch01.independentIncrementsOfJointProductLawV2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T00:50:37.897257+00:00
-- url     : https://prove2.me/submissions/77ff727b-5452-45f9-801e-27e7f6860cdd

import Mathlib
import Definitions.Def_LeanLevy_Processes_StochasticProcess
open MeasureTheory ProbabilityTheory
open scoped NNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (T : ℝ≥0 → Ω → ℝ)
    (hMeas : ∀ s : ℝ≥0, AEMeasurable (T s) P)
    (hJoint : ∀ (n : ℕ) (t : Fin (n + 1) → ℝ≥0),
      Monotone t →
      P.map (fun (ω : Ω) (k : Fin n) =>
        increment T (t k.castSucc) (t k.succ) ω) =
      Measure.pi (fun k : Fin n =>
        P.map (increment T (t k.castSucc) (t k.succ)))) :
    HasIndependentIncrements T P := by
  intro n t ht
  have hA : ∀ k : Fin n,
      AEMeasurable
        (increment T (t k.castSucc) (t k.succ)) P := by
    intro k
    exact (hMeas (t k.succ)).sub (hMeas (t k.castSucc))
  exact (iIndepFun_iff_map_fun_eq_pi_map hA).2 (hJoint n t ht)
