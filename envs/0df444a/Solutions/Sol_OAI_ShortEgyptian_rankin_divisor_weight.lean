-- Prove2me | solution 1 for OAI.ShortEgyptian.rankin_divisor_weight
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T02:00:55.77111+00:00
-- url     : https://prove2.me/submissions/765db216-de48-4b51-9df9-21a9873a6a20

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/DivisorWeights.lean:L126-L153
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.rankin_divisor_weight. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ShortEgyptianFractions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_Basic
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FirstDerivative
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ReciprocalDifferences
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IntervalDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_IteratedDifferencing
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ParameterBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_FourierDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowSpectrum
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_WindowDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_EmpiricalDiscrepancy
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorWeights
import Theorems.Thm_OAI_ShortEgyptian_smooth_divisor_weight

-- ---- from OAI.NumberTheory.ShortEgyptian.DivisorWeights ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

theorem rankin_divisor_weight (r : ℕ) (A lam : ℝ) (hA : 0 < A)
    (hlam : 0 ≤ lam) (hlamsmall : lam ≤ 1/2) (s P : Finset ℕ)
    (hs : ∀ d ∈ s, d ∈ Nat.factoredNumbers P ∧ A ≤ d) :
    ∑ d ∈ s, (d.divisors.card : ℝ)^r / d ≤
      Real.exp (-lam * Real.log A + momentSeriesConst r *
        ∑ p ∈ P with p.Prime, (p:ℝ)^(-(1-lam))) := by
  have hnonneg : 0 ≤ A ^ (-lam) := Real.rpow_nonneg hA.le _
  have hsum := smooth_divisor_weight r (by linarith : 1/2 ≤ 1-lam) s P (fun d hd => (hs d hd).1)
  calc
    _ ≤ ∑ d ∈ s, A^(-lam) * divisorWeight r (1-lam) d := by
      apply sum_le_sum
      intro d hd
      have hdpos : 0 < (d:ℝ) := lt_of_lt_of_le hA (hs d hd).2
      have hp : (d:ℝ)^(-lam) ≤ A^(-lam) :=
        Real.rpow_le_rpow_of_nonpos hA (hs d hd).2 (by linarith)
      have heq : (d.divisors.card : ℝ)^r / d =
          (d:ℝ)^(-lam) * divisorWeight r (1-lam) d := by
        unfold divisorWeight
        rw [mul_left_comm, ← Real.rpow_add hdpos]
        have hh : -lam + -(1-lam) = (-1:ℝ) := by ring
        rw [hh, Real.rpow_neg_one]
        ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hp (by unfold divisorWeight; positivity)
    _ = A^(-lam) * ∑ d ∈ s, divisorWeight r (1-lam) d := (mul_sum _ _ _).symm
    _ ≤ A^(-lam) * Real.exp (momentSeriesConst r *
        ∑ p ∈ P with p.Prime, (p:ℝ)^(-(1-lam))) := mul_le_mul_of_nonneg_left hsum hnonneg
    _ = _ := by rw [Real.rpow_def_of_pos hA, ← Real.exp_add]; congr 1; ring

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.rankin_divisor_weight := @_root_.OAI.ShortEgyptian.rankin_divisor_weight
