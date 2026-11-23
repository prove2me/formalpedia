-- Prove2me | solution 1 for Kyprianou.Ch01.pmfNatLaplaceDifferenceHasSumZero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-23T07:38:09.223816+00:00
-- url     : https://prove2.me/submissions/68bf27d9-30e6-4864-bace-5c5d2f65d791

import Mathlib
import Definitions.Def_Kyprianou_Ch01_BranchingClocks
import Theorems.Thm_Kyprianou_Ch01_pmfNatWeightedPowersSummable
import Theorems.Thm_Kyprianou_Ch01_expNegLogNatPow
open Kyprianou.Ch01 MeasureTheory Filter Set
open scoped NNReal ENNReal BigOperators
set_option autoImplicit false

theorem solution
    (p r : PMF ℕ)
    (hLaplace : ∀ (q : ℝ), 0 < q →
      (∑' n : ℕ, (p n).toReal * Real.exp (-q * (n : ℝ))) =
      (∑' n : ℕ, (r n).toReal * Real.exp (-q * (n : ℝ)))) :
    ∀ z : ℝ, 0 < z → z ≤ (1/2 : ℝ) →
      HasSum (fun n : ℕ =>
        z ^ n * ((p n).toReal - (r n).toReal)) 0  := by
  intro z hz hz2
  have hz1 : z ≤ 1 := by linarith
  have hlog : 0 < -Real.log z :=
    neg_pos.mpr (Real.log_neg hz (by linarith))
  have hexp (n : ℕ) :=
    Kyprianou.Ch01.expNegLogNatPow z hz n
  have hpW :=
    Kyprianou.Ch01.pmfNatWeightedPowersSummable p z hz.le hz1
  have hrW :=
    Kyprianou.Ch01.pmfNatWeightedPowersSummable r z hz.le hz1
  have heq :
      (∑' n : ℕ, z ^ n * (p n).toReal) =
      (∑' n : ℕ, z ^ n * (r n).toReal) := by
    have he := hLaplace (-Real.log z) hlog
    simp only [hexp] at he
    simpa only [mul_comm] using he
  have hsum := hpW.hasSum.sub hrW.hasSum
  have hsum2 : HasSum
      (fun n : ℕ => z ^ n * ((p n).toReal - (r n).toReal))
      ((∑' n : ℕ, z ^ n * (p n).toReal) -
        (∑' n : ℕ, z ^ n * (r n).toReal)) := by
    simpa only [mul_sub] using hsum
  simpa only [heq, sub_self] using hsum2
