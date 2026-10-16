-- Prove2me | solution 1 for OAI.ShortEgyptian.terminal_tail_subset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-16T03:07:07.997219+00:00
-- url     : https://prove2.me/submissions/a285d7cf-f075-473e-9338-112d6eb49a37

-- Generated from openai/math@1581d4c lean/OAI/NumberTheory/ShortEgyptian/SelectionBounds.lean:L49-L62
-- (upload_full_project.md Phase 4): solution for node OAI.ShortEgyptian.terminal_tail_subset. The node keeps its source
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
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_TruncatedDivisors
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SmoothBounds
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_DivisorMoments
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeLists
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_PrimeProducts
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_HammingDistance
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_SamplePartitions
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ProductCorrelations
import Definitions.Def_OAI_NumberTheory_ShortEgyptian_ListSelection

-- ---- from OAI.NumberTheory.ShortEgyptian.SelectionBounds ----
namespace OAI

namespace ShortEgyptian

open scoped BigOperators
open Finset

lemma reciprocal_gap (u : ℕ) (hu : 2 ≤ u) :
    (1:ℝ)/(u:ℝ)^5 ≤ 1/(u-1:ℕ)-1/u := by
  have huR : (2:ℝ) ≤ u := by exact_mod_cast hu
  have hu0 : (u:ℝ) ≠ 0 := by linarith
  have hu1 : (u:ℝ)-1 ≠ 0 := by linarith
  rw [Nat.cast_sub (by omega : 1 ≤ u),Nat.cast_one]
  have heq : (1:ℝ)/((u:ℝ)-1)-1/u = 1/((u:ℝ)*((u:ℝ)-1)) := by field_simp; ring
  rw [heq]
  apply one_div_le_one_div_of_le (mul_pos (by linarith) (by linarith))
  have h2 : (u:ℝ)^2 ≤ u^5 := pow_le_pow_right₀ (by linarith) (by norm_num : 2 ≤ 5)
  nlinarith

lemma finite_terminal_tail (N : ℕ) :
    ∑ u ∈ Icc 3 N, Real.exp (-5*Real.log u) ≤ (1/2:ℝ) := by
  have heq (u : ℕ) (hu : 3 ≤ u) : Real.exp (-5*Real.log u) = 1/(u:ℝ)^5 := by
    have huR : 0 < (u:ℝ) := by exact_mod_cast (show 0 < u by omega)
    rw [neg_mul,Real.exp_neg]
    rw [show (5:ℝ)*Real.log u = (5:ℕ)*Real.log u by norm_num,Real.exp_nat_mul,Real.exp_log huR]
    rw [one_div]
  have hsum (n : ℕ) (hn : 2 ≤ n) :
      ∑ u ∈ Icc 3 n, ((1:ℝ)/(u-1:ℕ)-1/u) = 1/2-1/n := by
    induction n,hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
      rw [sum_Icc_succ_top (by omega),ih]
      simp only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one]
      ring
  by_cases hN : 2 ≤ N
  · calc
      _ ≤ ∑ u ∈ Icc 3 N, ((1:ℝ)/(u-1:ℕ)-1/u) := by
        apply sum_le_sum
        intro u hu
        rw [heq u (mem_Icc.mp hu).1]
        exact reciprocal_gap u (by have := (mem_Icc.mp hu).1; omega)
      _ = 1/2-1/N := hsum N hN
      _ ≤ _ := sub_le_self _ (by positivity)
  · have hempty : Icc 3 N = ∅ := Icc_eq_empty_of_lt (by omega)
    simp [hempty]

lemma terminal_tail_subset (U : Finset ℕ) (hU : ∀ u ∈ U, 3 ≤ u) :
    ∑ u ∈ U, (Real.exp (-(1/200:ℝ)*Real.log u))^1000 ≤ (1/2:ℝ) := by
  have heq (u : ℕ) : (Real.exp (-(1/200:ℝ)*Real.log u))^1000 = Real.exp (-5*Real.log u) := by
    rw [←Real.exp_nat_mul]
    congr 1
    norm_num
    ring
  simp_rw [heq]
  apply le_trans _ (finite_terminal_tail (U.sup id))
  apply sum_le_sum_of_subset_of_nonneg
  · intro u hu
    exact mem_Icc.mpr ⟨hU u hu,le_sup (f := id) hu⟩
  · intro _ _ _
    exact Real.exp_nonneg _

end ShortEgyptian

end OAI

-- ---- platform node ----
open OAI OAI.ShortEgyptian
open scoped BigOperators
open Finset


theorem solution : type_of% @_root_.OAI.ShortEgyptian.terminal_tail_subset := @_root_.OAI.ShortEgyptian.terminal_tail_subset
