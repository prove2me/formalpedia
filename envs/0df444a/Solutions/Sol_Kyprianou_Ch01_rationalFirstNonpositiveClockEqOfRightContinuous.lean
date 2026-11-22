-- Prove2me | solution 1 for Kyprianou.Ch01.rationalFirstNonpositiveClockEqOfRightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:19:49.274207+00:00
-- url     : https://prove2.me/submissions/61d08ffb-56e5-4ed9-acb7-c32b31d77135

import Mathlib
import Definitions.Def_Kyprianou_Ch01_ForwardLampertiPaths
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- The closed first-nonpositive clock of an integer-valued right-continuous
path is recovered by a rational clock. -/
theorem solution
    (f : ℝ≥0 → ℤ)
    (hright : ∀ t : ℝ≥0, ContinuousWithinAt f (Set.Ici t) t) :
    (sInf {y : WithTop ℝ≥0 |
      ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = y ∧ f u ≤ 0}) =
    ⨅ r : ℚ,
      if f (Real.toNNReal (r : ℝ)) ≤ 0 then
        ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
      else ⊤ := by
  let k : ℚ → ℝ≥0 := fun r => Real.toNNReal (r : ℝ)
  let C : ℚ → WithTop ℝ≥0 :=
    fun r => if f (k r) ≤ 0 then (k r : WithTop ℝ≥0) else ⊤
  let S : Set (WithTop ℝ≥0) :=
    {y | ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = y ∧ f u ≤ 0}
  change sInf S = ⨅ r, C r
  apply le_antisymm
  · apply le_iInf
    intro r
    by_cases h : f (k r) ≤ 0
    · rw [show C r = (k r : WithTop ℝ≥0) from if_pos h]
      exact sInf_le ⟨k r, rfl, h⟩
    · simp [C, h]
  · apply le_sInf
    rintro _ ⟨u, rfl, hfu⟩
    by_contra! hlt
    obtain ⟨w, huw, hw⟩ := exists_between hlt
    obtain ⟨v, rfl⟩ :=
      WithTop.ne_top_iff_exists.mp (ne_of_lt (hw.trans_le le_top))
    have hmem : f u ∈ Set.Iio (1 : ℤ) := by
      change f u < 1
      omega
    obtain ⟨b, hub, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.mp
        ((hright u) (Iio_mem_nhds hmem))
    obtain ⟨r, hur, hrm⟩ := exists_rat_btwn
      (show (u : ℝ) < (min v b : ℝ≥0) by
        exact_mod_cast lt_min (WithTop.coe_lt_coe.mp huw) hub)
    have hcoe : (k r : ℝ) = (r : ℝ) :=
      Real.coe_toNNReal _ (by linarith [u.coe_nonneg])
    have huk : u < k r := by
      exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkm : k r < min v b := by
      exact_mod_cast (show (k r : ℝ) < (min v b : ℝ) by rwa [hcoe])
    have hlt1 : f (k r) < 1 :=
      hsub ⟨huk.le, hkm.trans_le (min_le_right _ _)⟩
    have hnonpos : f (k r) ≤ 0 := by omega
    have hkv : C r < (v : WithTop ℝ≥0) := by
      rw [show C r = (k r : WithTop ℝ≥0) from if_pos hnonpos]
      exact WithTop.coe_lt_coe.mpr
        (hkm.trans_le (min_le_left _ _))
    exact (not_le_of_gt (hkv.trans hw)) (iInf_le C r)
