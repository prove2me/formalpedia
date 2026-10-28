-- Prove2me | solution 1 for LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:20:12.381444+00:00
-- url     : https://prove2.me/submissions/de2de5bb-5597-4852-ba37-c5c60d0010ad

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ContinuityDyadicChaining

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ContinuityDyadicChaining.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal Topology
/-- **Dyadic scale selection.** For `0 < d ≤ 1` there is `m` with
`(1/2)^{m+1} < d ≤ (1/2)^m`. -/
lemma solution {d : ℝ} (hd0 : 0 < d) (hd1 : d ≤ 1) :
    ∃ m : ℕ, (1 / 2 : ℝ) ^ (m + 1) < d ∧ d ≤ (1 / 2) ^ m := by
  have hex : ∃ n : ℕ, (1 / 2 : ℝ) ^ n < d :=
    exists_pow_lt_of_lt_one hd0 (by norm_num)
  classical
  have hspec : (1 / 2 : ℝ) ^ Nat.find hex < d := Nat.find_spec hex
  have hpos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h | h
    · exfalso; rw [h] at hspec; simp at hspec; linarith
    · exact h
  refine ⟨Nat.find hex - 1, ?_, ?_⟩
  · rw [Nat.sub_add_cancel hpos]; exact hspec
  · have hmin := Nat.find_min hex (m := Nat.find hex - 1) (by omega)
    rw [not_lt] at hmin
    exact hmin
