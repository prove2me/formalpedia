-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.eventually_gridStop_lt_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:17:45.626717+00:00
-- url     : https://prove2.me/submissions/ba77df6e-5d37-4e81-a346-c0dcfd9c949b

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality
import Theorems.Thm_LevyStochCalc_Brownian_Ito_gridStopAux_le_iff_readable

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoLocality.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
universe u
variable {Ω : Type u} [MeasurableSpace Ω] {P : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure P]
  (τ : Ω → WithTop ℝ)
section GridStop
omit [MeasurableSpace Ω] [IsProbabilityMeasure P] in
/-- Eventually in the mesh, the grid stopping time falls strictly below any time the stopping
time has already passed. -/
theorem solution {t : ℝ} (ht : 0 < t) (ω : Ω) {s : ℝ} (hs : 0 < s) (hst : s ≤ t)
    (hτs : τ ω < ((s : ℝ) : WithTop ℝ)) :
    ∀ᶠ n in Filter.atTop, LevyStochCalc.Brownian.Ito.gridStop τ t n ω < ((s : ℝ) : WithTop ℝ) := by
  have hne : τ ω ≠ ⊤ := by
    intro h
    rw [h] at hτs
    exact absurd hτs (by simp)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  have hrs : r < s := by
    rw [← hr] at hτs
    exact_mod_cast hτs
  set u : ℝ := max r 0 with hu
  have hu0 : 0 ≤ u := le_max_right r 0
  have hus : u < s := max_lt hrs hs
  have hpos : 0 < s - u := sub_pos.mpr hus
  obtain ⟨N, hN⟩ := exists_nat_gt (t / (s - u))
  refine Filter.eventually_atTop.mpr ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right N 1) hn
  have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_left N 1) hn
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hstep : t / (n : ℝ) < s - u := by
    have h1 : t / (s - u) < (n : ℝ) := lt_of_lt_of_le hN hnN
    rw [div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hpos] at h1
    linarith
  set j : ℕ := ⌊u * (n : ℝ) / t⌋₊ + 1 with hj
  have hfl : (⌊u * (n : ℝ) / t⌋₊ : ℝ) ≤ u * (n : ℝ) / t :=
    Nat.floor_le (by positivity)
  have hfl' : u * (n : ℝ) / t < (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 :=
    Nat.lt_floor_add_one _
  have hjc : (j : ℝ) = (⌊u * (n : ℝ) / t⌋₊ : ℝ) + 1 := by
    rw [hj]
    push_cast
    ring
  have hgu : u < LevyStochCalc.Brownian.Ito.gridPt t n j := by
    rw [LevyStochCalc.Brownian.Ito.gridPt, lt_div_iff₀ hnpos, hjc]
    have := hfl'
    rw [div_lt_iff₀ ht] at this
    nlinarith
  have hgs : LevyStochCalc.Brownian.Ito.gridPt t n j < s := by
    have hle : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ u + t / (n : ℝ) := by
      rw [LevyStochCalc.Brownian.Ito.gridPt, hjc, div_le_iff₀ hnpos]
      have := hfl
      rw [le_div_iff₀ ht] at this
      field_simp
      nlinarith
    linarith
  have hjn : j ≤ n := by
    by_contra hcon
    push Not at hcon
    have : t ≤ LevyStochCalc.Brownian.Ito.gridPt t n j := by
      rw [LevyStochCalc.Brownian.Ito.gridPt, le_div_iff₀ hnpos]
      have : (n : ℝ) ≤ (j : ℝ) := by exact_mod_cast hcon.le
      nlinarith
    linarith
  have hstep' : LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n j) ω = ((LevyStochCalc.Brownian.Ito.gridPt t n j : ℝ) : WithTop ℝ) := by
    rw [LevyStochCalc.Brownian.Ito.stepStop, if_neg]
    rw [← hr]
    intro hcon
    have : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ r := by exact_mod_cast hcon
    have : LevyStochCalc.Brownian.Ito.gridPt t n j ≤ u := le_trans this (le_max_left r 0)
    linarith
  calc LevyStochCalc.Brownian.Ito.gridStop τ t n ω ≤ LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n j) ω :=
        (LevyStochCalc.Brownian.Ito.gridStopAux_le_iff_readable τ t n n ω _).mpr ⟨j, hjn, le_rfl⟩
    _ = ((LevyStochCalc.Brownian.Ito.gridPt t n j : ℝ) : WithTop ℝ) := hstep'
    _ < ((s : ℝ) : WithTop ℝ) := by exact_mod_cast hgs
