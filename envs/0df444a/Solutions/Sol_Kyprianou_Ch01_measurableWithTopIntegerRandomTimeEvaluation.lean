-- Prove2me | solution 1 for Kyprianou.Ch01.measurableWithTopIntegerRandomTimeEvaluation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T20:59:46.137602+00:00
-- url     : https://prove2.me/submissions/01d4f00f-ae82-4b8c-8f30-1fd51367fb08

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- A jointly measurable integer process can be evaluated at a measurable
possibly infinite random time, taking zero when the clock is infinite. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (F : ℝ≥0 → Ω → ℤ)
    (hJoint : Measurable (fun z : ℝ≥0 × Ω => F z.1 z.2))
    (T : Ω → WithTop ℝ≥0) (hT : Measurable T) :
    Measurable (fun ω : Ω =>
      (if T ω = ⊤ then (0 : ℤ)
       else F ((T ω).untopD 0) ω).toNat) := by
  have hClock : Measurable (fun ω : Ω => (T ω).untopD 0) :=
    hT.untopD 0
  have hValue : Measurable (fun ω : Ω => F ((T ω).untopD 0) ω) :=
    hJoint.comp (hClock.prodMk measurable_id)
  have hTop : MeasurableSet {ω : Ω | T ω = ⊤} :=
    (measurableSet_singleton (⊤ : WithTop ℝ≥0)).preimage hT
  have hZ : Measurable (fun ω : Ω =>
      if T ω = ⊤ then (0 : ℤ) else F ((T ω).untopD 0) ω) :=
    Measurable.ite hTop measurable_const hValue
  have hToNat : Measurable (fun z : ℤ => z.toNat) :=
    measurable_of_countable _
  exact hToNat.comp hZ
