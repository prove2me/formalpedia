-- Prove2me | solution 1 for Kyprianou.Ch01.pmfLaplaceStrictBelowOneOfPositiveOneAtom
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T08:52:21.873457+00:00
-- url     : https://prove2.me/submissions/1b8ff22f-fd74-4afa-a0a6-81ced5a049ea

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (p : PMF ℕ) (q : ℝ) (hq : 0 < q)
    (hp1 : 0 < (p 1).toReal) :
    (∑' n : ℕ,
      (p n).toReal * Real.exp (-q * (n : ℝ))) < 1 := by
  let W : ℕ → ℝ := fun n => Real.exp (-q * (n : ℝ))
  have hsum : Summable (fun n : ℕ => (p n).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hnonneg (n : ℕ) :
      0 ≤ (p n).toReal * W n :=
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hweight (n : ℕ) : W n ≤ 1 := by
    dsimp [W]
    apply Real.exp_le_one_iff.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hle (n : ℕ) :
      (p n).toReal * W n ≤ (p n).toReal :=
    mul_le_of_le_one_right ENNReal.toReal_nonneg (hweight n)
  have hexp : W 1 < 1 := by
    dsimp [W]
    apply Real.exp_lt_one_iff.mpr
    norm_num
    linarith
  have hlt : (p 1).toReal * W 1 < (p 1).toReal := by
    nlinarith [mul_lt_mul_of_pos_left hexp hp1]
  have hltSum := Summable.tsum_lt_tsum_of_nonneg
    hnonneg hle hlt hsum
  have hsum1 : (∑' n : ℕ, (p n).toReal) = 1 := by
    rw [← ENNReal.tsum_toReal_eq (fun n => p.apply_ne_top n)]
    simp
  dsimp [W] at hltSum
  simpa [hsum1] using hltSum
