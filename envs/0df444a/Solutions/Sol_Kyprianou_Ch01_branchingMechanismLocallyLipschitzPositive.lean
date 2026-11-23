-- Prove2me | solution 1 for Kyprianou.Ch01.branchingMechanismLocallyLipschitzPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T09:29:27.936069+00:00
-- url     : https://prove2.me/submissions/2481aabf-9af0-4151-87b7-2e759d15a689

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Definitions.Def_Kyprianou_Ch01_BranchingGenerator
import Theorems.Thm_Kyprianou_Ch01_branchingMechanismExpSumCompactLipschitz
open Kyprianou.Ch01 MeasureTheory
open scoped NNReal ENNReal
set_option autoImplicit false

theorem solution
    (rate : ℝ) (offspring : PMF ℕ) :
    ∀ (a b : ℝ), 0 < a → a ≤ b →
      ∃ C : ℝ, 0 ≤ C ∧
        ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b,
          |branchingMechanism rate offspring y -
            branchingMechanism rate offspring x| ≤
            C * |y - x| := by
  intro a b ha hab
  let L : ℝ := a⁻¹ + Real.exp b
  let C : ℝ := |rate| * L
  have hL : 0 ≤ L := by
    dsimp [L]
    exact add_nonneg (inv_nonneg.mpr ha.le) (Real.exp_pos b).le
  refine ⟨C, mul_nonneg (abs_nonneg rate) hL, ?_⟩
  intro x hx y hy
  have h := Kyprianou.Ch01.branchingMechanismExpSumCompactLipschitz
    offspring a b ha hab x y hx hy
  have hm := mul_le_mul_of_nonneg_left h (abs_nonneg rate)
  change |rate * (∑' k : ℕ, (offspring k).toReal *
      (1 - Real.exp (-y * ((k : ℝ) - 1)))) -
      rate * (∑' k : ℕ, (offspring k).toReal *
      (1 - Real.exp (-x * ((k : ℝ) - 1))))| ≤ C * |y - x|
  rw [← mul_sub, abs_mul]
  simpa [C, L, mul_assoc] using hm
