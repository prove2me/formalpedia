-- Prove2me | solution 1 for Kyprianou.Ch01.mckeanDiscountedValue_rightStoppedMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T18:43:59.90744+00:00
-- url     : https://prove2.me/submissions/e1738418-31ec-4df9-a5b2-076915672878

import Mathlib
import Definitions.Def_Kyprianou_Ch01_McKeanRightContinuousFiltration
import Definitions.Def_Kyprianou_Ch01_McKeanBrownianStopping
import Theorems.Thm_Kyprianou_Ch01_rightNaturalStoppingTime_measurable
import Theorems.Thm_Kyprianou_Ch01_mckeanValue_measurable
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation

open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Continuous paths permit stopped evaluation in the right-natural filtration. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ≥0 → Ω → ℝ)
    (x K q phi : ℝ)
    (hXmeas : ∀ t : ℝ≥0, Measurable (X t))
    (hAllContinuous : ∀ ω, Continuous (fun t : ℝ≥0 => X t ω))
    (tau : Ω → WithTop ℝ≥0)
    (hTau : IsNaturalRightStoppingTime (fun t ω => x + X t ω) tau) :
    let barrier := Real.log (K * phi / (1 + phi))
    Measurable (fun ω =>
      match tau ω with
      | none => (0 : ℝ)
      | some t => Real.exp (-q * (t : ℝ)) *
          mckeanValue K barrier phi (x + X t ω)) := by
  dsimp only
  classical
  let b : ℝ := Real.log (K * phi / (1 + phi))
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
  have hMc : Measurable (fun ω : Ω =>
      mckeanValue K b phi (x + X ((tau ω).untopD 0) ω)) :=
    (Kyprianou.Ch01.mckeanValue_measurable K b phi).comp
      (measurable_const.add hValue)
  have hDiscount :
      Measurable (fun ω : Ω =>
        Real.exp (-q * (((tau ω).untopD 0 : ℝ≥0) : ℝ))) := by
    fun_prop
  have hFiniteReward :
      Measurable (fun ω : Ω =>
        Real.exp (-q * (((tau ω).untopD 0 : ℝ≥0) : ℝ)) *
          mckeanValue K b phi (x + X ((tau ω).untopD 0) ω)) :=
    hDiscount.mul hMc
  have hTop : MeasurableSet {ω : Ω | tau ω = ⊤} :=
    hTm (measurableSet_singleton ⊤)
  have hEq :
      (fun ω : Ω =>
        match tau ω with
        | none => (0 : ℝ)
        | some t => Real.exp (-q * (t : ℝ)) *
            mckeanValue K b phi (x + X t ω)) =
      (fun ω : Ω =>
        if tau ω = ⊤ then 0
        else Real.exp (-q * (((tau ω).untopD 0 : ℝ≥0) : ℝ)) *
          mckeanValue K b phi (x + X ((tau ω).untopD 0) ω)) := by
    funext ω
    cases ht : tau ω with
    | top => simp [ht]
    | coe t =>
        have hne : (t : WithTop ℝ≥0) ≠ ⊤ := WithTop.coe_ne_top
        simp only [ht]
        rw [if_neg hne, WithTop.untopD_coe]
  rw [show Real.log (K * phi / (1 + phi)) = b from rfl]
  rw [hEq]
  exact Measurable.ite hTop measurable_const hFiniteReward
