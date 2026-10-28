-- Prove2me | solution 1 for LevyStochCalc.Brownian.Ito.exists_unifGrid_cell_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T14:18:20.408648+00:00
-- url     : https://prove2.me/submissions/bb918cd6-bce7-4cb0-b435-4dabd0b6b30a

import Definitions.Def_KLSModular_LevyStochCalc_Brownian_ItoFormulaGrid

/-
Copyright (c) 2026 Christian Garry. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Garry
-/
-- Vendored from https://github.com/cgarryZA/LevyStochCalc at commit 984dbf0b790031eac05d56fe5a84b65e15e1e932 (upstream path LevyStochCalc/Brownian/ItoFormulaGrid.lean; Apache-2.0; provenance in formalization/vendor/vendor-lock.json of the KLS repository)
open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
universe u
variable {Ω : Type u} [MeasurableSpace Ω]
/-- Every time in `(0, T]` lies in exactly one cell of the uniform grid. -/
theorem solution {T : ℝ} (hT : 0 < T) {m : ℕ} (hm0 : m ≠ 0) {s : ℝ}
    (hs : 0 < s) (hsT : s ≤ T) :
    ∃ i : ℕ, i < m ∧ LevyStochCalc.Brownian.Ito.unifGrid T m i < s ∧ s ≤ LevyStochCalc.Brownian.Ito.unifGrid T m (i + 1) := by
  have hmR : (0 : ℝ) < (m : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hm0)
  set x : ℝ := s * (m : ℝ) / T with hxdef
  have hx0 : 0 < x := by rw [hxdef]; positivity
  have hxm : x ≤ (m : ℝ) := by
    rw [hxdef, div_le_iff₀ hT]
    nlinarith [hmR.le]
  set k : ℕ := ⌈x⌉₊ with hkdef
  have hk1 : 1 ≤ k := Nat.ceil_pos.mpr hx0
  have hkm : k ≤ m := Nat.ceil_le.mpr (by exact_mod_cast hxm)
  refine ⟨k - 1, by omega, ?_, ?_⟩
  · have hcast : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [LevyStochCalc.Brownian.Ito.unifGrid, hcast, div_lt_iff₀ hmR]
    have hlt : (k : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0.le
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]
  · have hcast : (((k - 1 : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) := by
      have : (1 : ℕ) ≤ k := hk1
      push_cast [Nat.cast_sub this]
      ring
    rw [LevyStochCalc.Brownian.Ito.unifGrid, hcast, le_div_iff₀ hmR]
    have hle : x ≤ (k : ℝ) := Nat.le_ceil x
    have hxs : x * T = s * (m : ℝ) := by
      rw [hxdef]; field_simp
    nlinarith [hT, hmR]
