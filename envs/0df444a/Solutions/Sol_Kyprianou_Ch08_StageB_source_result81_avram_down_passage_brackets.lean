-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_avram_down_passage_brackets
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T08:20:23.123395+00:00
-- url     : https://prove2.me/submissions/943e5a2d-a086-4d84-9e1d-fddc27ab8871

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
import Theorems.Thm_AvramDividend_Classical_levy_path_bddBelow_finite_horizon
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Order.LeftRightNhds

open AvramDividend.Classical
open MeasureTheory ProbabilityTheory Filter Set Topology Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

private theorem strict_crossing_at_or_after_clock
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P F)
    (x : ℝ) (ω : Ω) (u : ℝ≥0) (hu : x + X.X u ω < 0) :
    tauMinus (shifted X.X x) 0 ω ≤ (u : WithTop ℝ≥0) := by
  change sInf {t : WithTop ℝ≥0 | ∃ v : ℝ≥0,
    0 < v ∧ (v : WithTop ℝ≥0) = t ∧ x + X.X v ω < 0} ≤ _
  by_cases hpos : 0 < u
  · exact sInf_le ⟨u, hpos, rfl, hu⟩
  have hu0 : u = 0 := le_antisymm (le_of_not_gt hpos) zero_le
  subst u
  let T := {t : WithTop ℝ≥0 | ∃ v : ℝ≥0,
    0 < v ∧ (v : WithTop ℝ≥0) = t ∧ x + X.X v ω < 0}
  change sInf T ≤ (0 : WithTop ℝ≥0)
  by_contra! hclock
  obtain ⟨w, hw, hws⟩ := exists_between hclock
  obtain ⟨r, rfl⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt (hws.trans_le le_top))
  have hr : 0 < r := WithTop.coe_lt_coe.mp hw
  have hrc : ContinuousWithinAt (fun t : ℝ≥0 => x + X.X t ω) (Ici 0) 0 :=
    continuousWithinAt_const.add (X.rightCont ω 0)
  obtain ⟨b, hb, hsub⟩ :=
    mem_nhdsGE_iff_exists_Ico_subset.mp (hrc (isOpen_Iio.mem_nhds hu))
  obtain ⟨v, hv0, hv⟩ := exists_between (lt_min hb hr)
  have hvx : x + X.X v ω < 0 := hsub ⟨hv0.le, hv.trans_le (min_le_left _ _)⟩
  have hvt : (v : WithTop ℝ≥0) < sInf T :=
    (WithTop.coe_lt_coe.mpr (hv.trans_le (min_le_right _ _))).trans hws
  exact (not_le_of_gt hvt) (sInf_le ⟨v, hv0, rfl, hvx⟩)

theorem solution
    {Ω : Type} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration ℝ≥0 mΩ}
    (X : AvramDividend.Classical.SpectrallyNegativeLevy P F)
    (x : ℝ) (ω : Ω) (t : ℝ≥0) :
    let τ := tauMinus (shifted X.X x) 0 ω
    let R := -sInf {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X.X u ω}
    (τ < (t : WithTop ℝ≥0) → x < R) ∧ (x < R → τ ≤ (t : WithTop ℝ≥0)) := by
  intro τ R
  let S := {y : ℝ | ∃ u : ℝ≥0, u ≤ t ∧ y = X.X u ω}
  have hRs : R = -sInf S := rfl
  have hS : S.Nonempty := ⟨X.X 0 ω, 0, zero_le, rfl⟩
  have hSb : BddBelow S := levy_path_bddBelow_finite_horizon X t ω
  constructor
  · intro h
    change sInf {v : WithTop ℝ≥0 | ∃ u : ℝ≥0,
      0 < u ∧ (u : WithTop ℝ≥0) = v ∧ x + X.X u ω < 0} < _ at h
    obtain ⟨_, ⟨u, _, rfl, hux⟩, hu⟩ := sInf_lt_iff.mp h
    have hi := csInf_le hSb
      (show X.X u ω ∈ S from ⟨u, (WithTop.coe_lt_coe.mp hu).le, rfl⟩)
    linarith
  · intro h
    have hHit : ∃ u : ℝ≥0, u ≤ t ∧ x + X.X u ω < 0 := by
      by_contra! hnone
      have hbound : -x ≤ sInf S := by
        apply le_csInf hS
        rintro _ ⟨u, hu, rfl⟩
        linarith [hnone u hu]
      linarith
    obtain ⟨u, hu, hux⟩ := hHit
    exact (strict_crossing_at_or_after_clock X x ω u hux).trans (WithTop.coe_le_coe.mpr hu)
