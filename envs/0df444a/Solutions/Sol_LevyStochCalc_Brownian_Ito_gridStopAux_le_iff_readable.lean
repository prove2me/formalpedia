-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.gridStopAux_le_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:05:17.345114+00:00
-- url     : https://prove2.me/submissions/7bd9608b-1803-45d5-89bf-82c02ef454f4

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoLocality

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
theorem solution (t : ℝ) (n k : ℕ) (ω : Ω) (a : WithTop ℝ) :
    LevyStochCalc.Brownian.Ito.gridStopAux τ t n k ω ≤ a ↔ ∃ j ≤ k, LevyStochCalc.Brownian.Ito.stepStop τ (LevyStochCalc.Brownian.Ito.gridPt t n j) ω ≤ a := by
  induction k with
  | zero =>
    constructor
    · intro h
      exact ⟨0, le_rfl, h⟩
    · rintro ⟨j, hj, hjle⟩
      rw [Nat.le_zero] at hj
      subst hj
      exact hjle
  | succ k ih =>
    rw [LevyStochCalc.Brownian.Ito.gridStopAux, min_le_iff, ih]
    constructor
    · rintro (h | ⟨j, hj, hjle⟩)
      · exact ⟨k + 1, le_rfl, h⟩
      · exact ⟨j, hj.trans (Nat.le_succ k), hjle⟩
    · rintro ⟨j, hj, hjle⟩
      rcases Nat.lt_or_ge j (k + 1) with hlt | hge
      · exact Or.inr ⟨j, Nat.lt_succ_iff.mp hlt, hjle⟩
      · have : j = k + 1 := le_antisymm hj hge
        subst this
        exact Or.inl hjle
