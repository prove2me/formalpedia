-- Prove2me | solution 1 for Kyprianou.Ch04.openHitLtRationalWitness
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-26T08:08:15.208005+00:00
-- url     : https://prove2.me/submissions/c5908119-8639-4d91-829f-88ebdbc38c94

import Mathlib
open MeasureTheory Filter Set Topology
open scoped NNReal
set_option autoImplicit false

/-- Strict open hitting before a finite clock is witnessed at a rational time. -/
theorem solution (Y : NNReal → ℝ) (B : Set ℝ) (hB : IsOpen B)
    (hrc : ∀ t : NNReal, ContinuousWithinAt Y (Set.Ici t) t) (s : NNReal) :
    sInf {u : WithTop NNReal | ∃ r : NNReal, u = ↑r ∧ Y r ∈ B} <
      (s : WithTop NNReal) ↔
      ∃ q : ℚ, 0 < q ∧ (q : ℝ) < s ∧ Y (Real.toNNReal q) ∈ B := by
  constructor
  · intro h
    obtain ⟨_, ⟨t, rfl, htB⟩, hts⟩ := sInf_lt_iff.mp h
    have hts' : t < s := WithTop.coe_lt_coe.mp hts
    have hev : ∀ᶠ v in 𝓝[≥] t, Y v ∈ B :=
      (hrc t).eventually (hB.mem_nhds htB)
    obtain ⟨w, htw, hw⟩ := mem_nhdsGE_iff_exists_Ico_subset.mp hev
    have hmin : (t : ℝ) < min (w : ℝ) s :=
      lt_min (by exact_mod_cast htw) (by exact_mod_cast hts')
    obtain ⟨q, htq, hqm⟩ := exists_rat_btwn hmin
    have hq0 : (0 : ℝ) < q := (NNReal.coe_nonneg t).trans_lt htq
    refine ⟨q, by exact_mod_cast hq0, hqm.trans_le (min_le_right _ _), hw ?_⟩
    constructor
    · rw [Real.le_toNNReal_iff_coe_le hq0.le]; exact htq.le
    · rw [Real.toNNReal_lt_iff_lt_coe hq0.le]; exact hqm.trans_le (min_le_left _ _)
  · rintro ⟨q, hq0, hqs, hqB⟩
    have hq0' : (0 : ℝ) < q := by exact_mod_cast hq0
    refine lt_of_le_of_lt (sInf_le ⟨Real.toNNReal q, rfl, hqB⟩) ?_
    rw [WithTop.coe_lt_coe, Real.toNNReal_lt_iff_lt_coe hq0'.le]
    exact hqs
