-- Prove2me | solution 1 for Kyprianou.Ch04.exercise41PathCompactV10
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T12:44:48.308431+00:00
-- url     : https://prove2.me/submissions/86d81adf-7dbc-4a11-89ac-b3d1291a92d9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_Kyprianou_Ch01_cadlag_runningSup_bddAbove
import Definitions.Def_Kyprianou_Ch02_LargeJumpProcess
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_Kyprianou_Ch04_PathJumpAndItoIntegral
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical Kyprianou.Ch04
open scoped NNReal ENNReal BigOperators Classical Topology
set_option autoImplicit false
theorem solution
    {Ω : Type} (X Xleft : NNReal → Ω → ℝ) (w : Ω)
    (hCadlag : IsCadlag (fun t : NNReal => X t w))
    (hLeft : ∀ t : NNReal, 0 < t →
      Tendsto (fun s => X s w) (nhdsWithin t (Iio t)) (nhds (Xleft t w)))
    (t : NNReal) :
    Measurable (fun s : ℝ => X s.toNNReal w) ∧
    ∃ R : ℝ, 0 < R ∧ (∀ s : NNReal, s ≤ t → |X s w| ≤ R) ∧
      (∀ s : NNReal, 0 < s → s ≤ t → |Xleft s w| ≤ R) := by
  have hJoint := rightContinuous_measurable_sections_joint_evaluation
    (fun s (_ : Unit) => X s w) (fun _ => measurable_const)
    (fun _ s => (hCadlag s).1)
  have hM : Measurable (fun s : NNReal => X s w) :=
    hJoint.comp (measurable_id.prodMk (measurable_const : Measurable (fun _ : NNReal => ((): Unit))))
  refine ⟨hM.comp measurable_real_toNNReal, ?_⟩
  have hAbs : IsCadlag (fun s : NNReal => |X s w|) := by
    intro s
    obtain ⟨hr,l,hl⟩ := hCadlag s
    exact ⟨continuous_abs.continuousAt.comp_continuousWithinAt hr,
      ⟨|l|, continuous_abs.continuousAt.tendsto.comp hl⟩⟩
  obtain ⟨M,hM⟩ := Kyprianou.Ch01.cadlag_runningSup_bddAbove _ hAbs t
  let R := max 1 M
  have hR : 0 < R := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hX (s : NNReal) (hs : s ≤ t) : |X s w| ≤ R :=
    (hM ⟨s,hs,rfl⟩).trans (le_max_right _ _)
  refine ⟨R,hR,hX,?_⟩
  intro s hp hs
  letI : NeBot (nhdsWithin s (Iio s)) := nhdsLT_neBot_of_exists_lt ⟨0,hp⟩
  apply le_of_tendsto (continuous_abs.continuousAt.tendsto.comp (hLeft s hp))
  filter_upwards [self_mem_nhdsWithin (s := Iio s) (a := s)] with u hu
  exact hX u (hu.le.trans hs)
