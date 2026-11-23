-- Prove2me | solution 1 for Kyprianou.Ch01.branchingOneAncestorLaplaceStrictPositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:16:20.503718+00:00
-- url     : https://prove2.me/submissions/cb20a0ba-3150-429a-9d45-b9923fe7afa1

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

/-- Every PMF has strictly positive exponential Laplace sum for a positive parameter. -/
theorem solution
    (law : PopulationLaws) :
    ∀ (t : ℝ≥0) (q : ℝ), 0 < q →
      0 < branchingLaplace law 1 t q := by
  intro t q hq
  let p : PMF ℕ := law 1 t
  have hsum : Summable (fun n : ℕ => (p n).toReal) :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  have hnonneg (n : ℕ) :
      0 ≤ (p n).toReal * Real.exp (-q * (n : ℝ)) :=
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  have hweight (n : ℕ) : Real.exp (-q * (n : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith
  have hle (n : ℕ) :
      (p n).toReal * Real.exp (-q * (n : ℝ)) ≤ (p n).toReal :=
    mul_le_of_le_one_right ENNReal.toReal_nonneg (hweight n)
  have hsumW : Summable (fun n : ℕ =>
      (p n).toReal * Real.exp (-q * (n : ℝ))) :=
    Summable.of_nonneg_of_le hnonneg hle hsum
  obtain ⟨n, hn⟩ := p.support_nonempty
  have hnpos : 0 < (p n).toReal :=
    ENNReal.toReal_pos ((p.mem_support_iff n).mp hn) (p.apply_ne_top n)
  have hpos : 0 < ∑' n : ℕ,
      (p n).toReal * Real.exp (-q * (n : ℝ)) :=
    hsumW.tsum_pos hnonneg n (mul_pos hnpos (Real.exp_pos _))
  simpa only [branchingLaplace, p] using hpos
