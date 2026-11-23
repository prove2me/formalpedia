-- Prove2me | solution 1 for Kyprianou.Ch08.StageB.rightContinuousStoppedRationalMarginImpliesStrict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T11:53:18.155393+00:00
-- url     : https://prove2.me/submissions/dfc6450f-5103-427d-8014-232b5b5ff70f

import Mathlib
import Theorems.Thm_Kyprianou_Ch08_StageB_rationalCutoffBetweenBeforeStop
set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem solution
    (f : ℝ≥0 → ℝ) (T : WithTop ℝ≥0) (h : ℝ)
    (hright : ∀ t : ℝ≥0,
      ContinuousWithinAt f (Set.Ici t) t)
    (hmargin : ∀ q : ℚ, 0 ≤ q →
      ((q : ℝ).toNNReal : WithTop ℝ≥0) < T →
      ∃ n : ℕ, ∀ r : ℚ, 0 ≤ r → r ≤ q →
        f (r : ℝ).toNNReal <
          h - 1 / (((n + 1 : ℕ) : ℝ))) :
    ∀ t : ℝ≥0, (t : WithTop ℝ≥0) < T → f t < h := by
  intro t htT
  obtain ⟨q, hqpos, htq, hqT⟩ :=
    Kyprianou.Ch08.StageB.rationalCutoffBetweenBeforeStop t T htT
  obtain ⟨n, hR⟩ := hmargin q hqpos hqT
  let c : ℝ := h - 1 / (((n + 1 : ℕ) : ℝ))
  have hc : c < h := by
    have hOne : (0 : ℝ) < 1 / (((n + 1 : ℕ) : ℝ)) := by positivity
    dsimp [c]
    linarith
  by_contra hnot
  have hge : h ≤ f t := le_of_not_gt hnot
  have hgt : c < f t := lt_of_lt_of_le hc hge
  obtain ⟨b, htb, hFuture⟩ :=
    mem_nhdsGE_iff_exists_Ico_subset.mp
      ((hright t) (Ioi_mem_nhds hgt))
  have hqnonneg : (0 : ℝ) ≤ (q : ℝ) := by
    exact_mod_cast hqpos
  have hqcoe : ((q : ℝ).toNNReal : ℝ) = (q : ℝ) :=
    Real.coe_toNNReal _ hqnonneg
  have htqReal : (t : ℝ) < (q : ℝ) := by
    have h := (show (t : ℝ) < ((q : ℝ).toNNReal : ℝ) by
      exact_mod_cast htq)
    rwa [hqcoe] at h
  have htbReal : (t : ℝ) < (b : ℝ) := by exact_mod_cast htb
  obtain ⟨r, htr, hrMin⟩ :=
    exists_rat_btwn (lt_min htqReal htbReal)
  have hrq : (r : ℝ) < (q : ℝ) :=
    hrMin.trans_le (min_le_left _ _)
  have hrb : (r : ℝ) < (b : ℝ) :=
    hrMin.trans_le (min_le_right _ _)
  have hrpos : (0 : ℝ) ≤ (r : ℝ) :=
    le_trans t.coe_nonneg (le_of_lt htr)
  have hrRat : 0 ≤ r := by exact_mod_cast hrpos
  have hrqRat : r ≤ q := by exact_mod_cast (le_of_lt hrq)
  have hrcoe : ((r : ℝ).toNNReal : ℝ) = (r : ℝ) :=
    Real.coe_toNNReal _ hrpos
  have hrt : t ≤ (r : ℝ).toNNReal := by
    exact_mod_cast (show (t : ℝ) ≤ ((r : ℝ).toNNReal : ℝ) by
      rw [hrcoe]
      exact le_of_lt htr)
  have hrbNN : (r : ℝ).toNNReal < b := by
    exact_mod_cast (show ((r : ℝ).toNNReal : ℝ) < (b : ℝ) by
      rw [hrcoe]
      exact hrb)
  have hFgt : c < f (r : ℝ).toNNReal :=
    hFuture ⟨hrt, hrbNN⟩
  have hFlt : f (r : ℝ).toNNReal < c := hR r hrRat hrqRat
  exact (not_lt_of_ge (le_of_lt hFgt)) hFlt
