-- Prove2me | solution 1 for Kyprianou.Ch04.kw48_Z_right_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-25T23:33:31.388856+00:00
-- url     : https://prove2.me/submissions/805511ea-8821-474c-aa86-1da14118a570

import Mathlib
import Definitions.Def_Kyprianou_Ch04_KW48Processes
import Theorems.Thm_AvramDividend_Classical_runningSup_continuous_actual
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_levy_joint_time_state_measurable
open MeasureTheory ProbabilityTheory AvramDividend.Classical Kyprianou.Ch04.KW48
open Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Reflected characteristic paths extended to real time are measurable
and right-continuous. -/
theorem solution {Ω : Type} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {F : Filtration NNReal mΩ}
    (L : SpectrallyNegativeLevy P F)
    (alpha beta : Real) (w : Ω) :
    Measurable (fun r : Real => Z L alpha beta r.toNNReal w) ∧
    ∀ r : Real, ContinuousWithinAt (fun x : Real =>
      Z L alpha beta x.toNNReal w) (Ici r) r := by
  have hMap : Measurable (fun r : NNReal => (r,w)) :=
    measurable_id.prodMk measurable_const
  have hU := (levy_runningSup_joint_time_path_measurable L).comp hMap
  have hX := (chat04_levy_joint_time_state_measurable L).comp hMap
  have hm : Measurable (fun r : NNReal => Z L alpha beta r w) := by
    unfold Z
    fun_prop (disch := assumption)
  refine ⟨hm.comp measurable_real_toNNReal,?_⟩
  intro r
  have hUcont := (runningSup_continuous_actual L w).continuousWithinAt
    (s := Ici r.toNNReal) (x := r.toNNReal)
  have hXcont := L.rightCont w r.toNNReal
  have hz : ContinuousWithinAt (fun s : NNReal => Z L alpha beta s w)
      (Ici r.toNNReal) r.toNNReal := by
    unfold Z
    fun_prop (disch := assumption)
  have hmap : MapsTo Real.toNNReal (Ici r) (Ici r.toNNReal) :=
    fun x hx => Real.toNNReal_le_toNNReal hx
  exact hz.comp continuous_real_toNNReal.continuousWithinAt hmap
