-- Prove2me | solution 1 for Kyprianou.Ch04.fixedHorizonSignedExtremaMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T17:11:43.656201+00:00
-- url     : https://prove2.me/submissions/58eaf3a9-1c7a-4579-aeeb-a9020581941a

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_levy_running_infimum_joint_time_path_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (F : Filtration NNReal (inferInstance : MeasurableSpace Ω))
    (L : SpectrallyNegativeLevy P F) (t : NNReal) :
    Measurable (fun w : Ω => L.X t w - sSup ((fun s : NNReal => L.X s w) '' Iic t)) ∧
    Measurable (fun w : Ω => sInf ((fun s : NNReal => L.X s w) '' Iic t)) := by
  have hS (w : Ω) : runningSup L t w = sSup ((fun s : NNReal => L.X s w) '' Iic t) := by
    rw [(runningSup_eq_rawSup_nonneg L t w).1]
    change sSup (range (fun s : Icc (0 : NNReal) t => L.X s.1 w)) = _
    congr 1
    ext y
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨s.1, s.2.2, rfl⟩
    · rintro ⟨s, hs, rfl⟩
      exact ⟨⟨s, zero_le, hs⟩, rfl⟩
  have hI (w : Ω) : ((fun s : NNReal => L.X s w) '' Iic t) =
      {y : ℝ | ∃ s : NNReal, s ≤ t ∧ y = L.X s w} := by
    ext y
    constructor <;> rintro ⟨s, hs, h⟩ <;> exact ⟨s, hs, h.symm⟩
  have hp : Measurable (fun w : Ω => (t,w)) := measurable_const.prodMk measurable_id
  constructor
  · simp_rw [← hS]
    exact L.adapted.measurable.sub ((levy_runningSup_joint_time_path_measurable L).comp hp)
  · have h := ((levy_running_infimum_joint_time_path_measurable L).comp hp).neg
    change Measurable (fun w : Ω => -(-sInf {y : ℝ | ∃ s : NNReal, s ≤ t ∧ y = L.X s w})) at h
    simpa only [neg_neg, hI] using h
