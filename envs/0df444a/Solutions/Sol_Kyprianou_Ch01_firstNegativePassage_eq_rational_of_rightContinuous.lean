-- Prove2me | solution 1 for Kyprianou.Ch01.firstNegativePassage_eq_rational_of_rightContinuous
-- status  : ACCEPTED   (prove)
-- author  : @pageman
-- created : 2026-11-24T19:00:06.00081+00:00
-- url     : https://prove2.me/submissions/19985c65-7a67-4a36-af4b-887b553e2412

import Mathlib
import Definitions.Def_Kyprianou_Ch01_LampertiInverse
open MeasureTheory ProbabilityTheory Kyprianou.Ch01 Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

/-- Under pathwise right-continuity, the strict-negative passage clock equals
its countable rational lower clock. -/
theorem solution
    {Ω : Type*} (X : ℝ≥0 → Ω → ℤ) (ω : Ω)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt (fun s : ℝ≥0 => X s ω) (Set.Ici t) t) :
    firstNegativePassage X ω =
      ⨅ r : ℚ,
        if 0 < (r : ℝ) ∧ X (Real.toNNReal (r : ℝ)) ω < 0 then
          ((Real.toNNReal (r : ℝ) : ℝ≥0) : WithTop ℝ≥0)
        else ⊤ := by
  classical
  let f : ℝ≥0 → ℤ := fun t => X t ω
  let k : ℚ → ℝ≥0 := fun r => Real.toNNReal (r : ℝ)
  let C : ℚ → WithTop ℝ≥0 := fun r =>
    if 0 < (r : ℝ) ∧ f (k r) < 0 then (k r : WithTop ℝ≥0) else ⊤
  let E : Set ℝ≥0 := {t | 0 < t ∧ f t < 0}
  let S : Set (WithTop ℝ≥0) :=
    {y | ∃ u : ℝ≥0, (u : WithTop ℝ≥0) = y ∧ 0 < u ∧ f u < 0}
  have him : S = (fun u : ℝ≥0 => (u : WithTop ℝ≥0)) '' E := by
    ext z
    constructor
    · rintro ⟨u, hu, h0, hf⟩
      exact ⟨u, ⟨h0, hf⟩, hu⟩
    · rintro ⟨u, ⟨h0, hf⟩, hu⟩
      exact ⟨u, hu, h0, hf⟩
  have hsource : firstNegativePassage X ω = sInf S := by
    change (if ∃ t : ℝ≥0, 0 < t ∧ f t < 0 then
        ((sInf E : ℝ≥0) : WithTop ℝ≥0)
      else ⊤) = sInf S
    by_cases he : E.Nonempty
    · have hh : ∃ t : ℝ≥0, 0 < t ∧ f t < 0 := he
      have hco : ((sInf E : ℝ≥0) : WithTop ℝ≥0) = sInf S := by
        rw [him]
        exact WithTop.coe_sInf' he (by bddDefault : BddBelow E)
      rw [if_pos hh, hco]
    · have hempty : E = ∅ := Set.not_nonempty_iff_eq_empty.mp he
      have hh : ¬ ∃ t : ℝ≥0, 0 < t ∧ f t < 0 := by
        rintro ⟨t, ht⟩
        exact he ⟨t, ht⟩
      rw [if_neg hh, him, hempty]
      simp only [Set.image_empty, sInf_empty]
  rw [hsource]
  change sInf S = ⨅ r, C r
  apply le_antisymm
  · apply le_iInf
    intro r
    by_cases h : 0 < (r : ℝ) ∧ f (k r) < 0
    · have hk0 : (0 : ℝ≥0) < k r := by
        have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ h.1.le
        exact NNReal.coe_pos.mp (hcoe.symm ▸ h.1)
      rw [show C r = (k r : WithTop ℝ≥0) from if_pos h]
      exact sInf_le ⟨k r, rfl, hk0, h.2⟩
    · rw [show C r = ⊤ from if_neg h]
      exact le_top
  · apply le_sInf
    rintro _ ⟨u, rfl, hu0, hfu⟩
    by_contra! hlt
    obtain ⟨w, huw, hw⟩ := exists_between hlt
    obtain ⟨v, rfl⟩ :=
      WithTop.ne_top_iff_exists.mp (ne_of_lt (hw.trans_le le_top))
    have hmem : f u ∈ Set.Iio (0 : ℤ) := hfu
    obtain ⟨b, hub, hsub⟩ :=
      mem_nhdsGE_iff_exists_Ico_subset.mp
        ((hright u) (Iio_mem_nhds hmem))
    -- pick a positive upper bound strictly above u
    obtain ⟨r, hur, hrm⟩ := exists_rat_btwn
      (show (u : ℝ) < (min v b : ℝ≥0) by
        exact_mod_cast lt_min (WithTop.coe_lt_coe.mp huw) hub)
    have hrpos : 0 < (r : ℝ) :=
      lt_trans (show (0 : ℝ) < (u : ℝ) from NNReal.coe_pos.mpr hu0) hur
    have hcoe : (k r : ℝ) = (r : ℝ) := Real.coe_toNNReal _ hrpos.le
    have huk : u < k r := by
      exact_mod_cast (show (u : ℝ) < (k r : ℝ) by rwa [hcoe])
    have hkm : k r < min v b := by
      exact_mod_cast (show (k r : ℝ) < (min v b : ℝ) by rwa [hcoe])
    have hlt0 : f (k r) < 0 :=
      hsub ⟨huk.le, hkm.trans_le (min_le_right _ _)⟩
    have hkv : C r < (v : WithTop ℝ≥0) := by
      rw [show C r = (k r : WithTop ℝ≥0) from if_pos ⟨hrpos, hlt0⟩]
      exact WithTop.coe_lt_coe.mpr (hkm.trans_le (min_le_left _ _))
    exact (not_le_of_gt (hkv.trans hw)) (iInf_le C r)
