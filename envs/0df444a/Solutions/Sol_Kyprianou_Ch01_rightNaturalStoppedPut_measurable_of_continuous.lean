-- Prove2me | solution 1 for Kyprianou.Ch01.rightNaturalStoppedPut_measurable_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:25:38.865291+00:00
-- url     : https://prove2.me/submissions/eac89160-20af-488c-8d0a-6ecb518f67c0

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingTime_measurable
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (x K q : ℝ)
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    Measurable (discountedPut X x K q tau) := by
  classical
  have hShift (t : ℝ≥0) :
      Measurable (fun ω : Ω => x + X t ω) :=
    measurable_const.add (hXmeas t)
  have hTm : Measurable tau :=
    Kyprianou.Ch01.rightNaturalStoppingTime_measurable
      (fun t ω => x + X t ω) hShift tau hTau
  have hTime :
      Measurable (fun ω : Ω => (tau ω).untopD (0 : ℝ≥0)) :=
    hTm.untopD 0
  have hJoint :
      Measurable (fun z : ℝ≥0 × Ω => X z.1 z.2) :=
    AvramDividend.Classical.rightContinuous_measurable_sections_joint_evaluation
      X hXmeas (fun ω t => (hAllContinuous ω).continuousWithinAt)
  have hPair :
      Measurable (fun ω : Ω => ((tau ω).untopD 0, ω)) :=
    Measurable.prod hTime measurable_id
  have hValue :
      Measurable (fun ω : Ω => X ((tau ω).untopD 0) ω) := by
    simpa only [Function.comp_def] using hJoint.comp hPair
  have hTimeReal :
      Measurable (fun ω : Ω => (((tau ω).untopD 0 : ℝ≥0) : ℝ)) :=
    Measurable.coe_nnreal_real hTime
  have hFiniteReward :
      Measurable (fun ω : Ω =>
        Real.exp (-q * (((tau ω).untopD 0 : ℝ≥0) : ℝ)) *
          max (K - Real.exp (x + X ((tau ω).untopD 0) ω)) 0) := by
    fun_prop
  have hTop : MeasurableSet {ω : Ω | tau ω = ⊤} :=
    hTm (measurableSet_singleton ⊤)
  have hEq :
      discountedPut X x K q tau =
        (fun ω : Ω =>
          if tau ω = ⊤ then 0
          else Real.exp (-q * (((tau ω).untopD 0 : ℝ≥0) : ℝ)) *
            max (K - Real.exp (x + X ((tau ω).untopD 0) ω)) 0) := by
    funext ω
    cases ht : tau ω with
    | top => simp [discountedPut, ht]
    | coe t =>
        have hne : (t : WithTop ℝ≥0) ≠ ⊤ := WithTop.coe_ne_top
        simp only [discountedPut, ht]
        rw [if_neg hne, WithTop.untopD_coe]
  rw [hEq]
  exact Measurable.ite hTop measurable_const hFiniteReward
