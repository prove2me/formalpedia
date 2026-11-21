-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.source_result81_strict_lower_clock_shift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T13:47:44.191334+00:00
-- url     : https://prove2.me/submissions/77ffcea7-cecb-4f25-b882-dc28e05c2b1d

import Definitions.Def_Kyprianou_Ch08_StageCFoundation_D
open Set Filter Topology MeasureTheory ProbabilityTheory Kyprianou.Ch08 Kyprianou.Ch08.StageB
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (f : ℝ≥0 → ℝ) (t : ℝ≥0)
    (hbefore : (t : WithTop ℝ≥0) < tauMinus (fun s (_ : Unit) => f s) 0 ()) :
    tauMinus (fun s (_ : Unit) => f s) 0 () =
      (t : WithTop ℝ≥0) + tauMinus (fun s (_ : Unit) => f (t + s)) 0 () := by
  let S : Set ℝ≥0∞ := {y | ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) = y ∧ f s < 0}
  let T : Set ℝ≥0∞ := {y | ∃ s : ℝ≥0, 0 < s ∧ (s : ℝ≥0∞) = y ∧ f (t + s) < 0}
  change (t : ℝ≥0∞) < sInf S at hbefore
  change sInf S = (t : ℝ≥0∞) + sInf T
  have himage : S = (fun y : ℝ≥0∞ => (t : ℝ≥0∞) + y) '' T := by
    ext y
    constructor
    · rintro ⟨s, hspos, rfl, hs⟩
      have hle : sInf S ≤ (s : ℝ≥0∞) := sInf_le ⟨s, hspos, rfl, hs⟩
      have hts : t < s := WithTop.coe_lt_coe.mp (hbefore.trans_le hle)
      refine ⟨(s - t : ℝ≥0), ⟨s - t, tsub_pos_of_lt hts, rfl, ?_⟩, ?_⟩
      · simpa only [add_tsub_cancel_of_le hts.le] using hs
      · change (t : ℝ≥0∞) + ((s - t : ℝ≥0) : ℝ≥0∞) = (s : ℝ≥0∞)
        rw [← ENNReal.coe_add, add_tsub_cancel_of_le hts.le]
    · rintro ⟨_, ⟨s, hspos, rfl, hs⟩, rfl⟩
      exact ⟨t + s, by positivity, ENNReal.coe_add _ _, hs⟩
  rw [himage, sInf_image, ENNReal.add_sInf]

