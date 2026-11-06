-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.prime_sixth_row_approx
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:25:09.277236+00:00
-- url     : https://prove2.me/submissions/7a65e9c5-7461-47b4-aaea-b6fc5e322ba0

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_RamifiedTracePhase
import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Theorems.Thm_OAI_ShortDraftLatticeCount_finite_divisible_count
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_difference_norm
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
attribute [local simp] OAI.IdealGaussCRT.traceProdChar_mk



set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (p : O) (hp : p ≠ 0) (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, p ∈ P i) → p ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
      (64 * (D / qNat p + 1) : ℕ) := by
  classical
  let S := columns.filter (fun n => ∃ i ∈ support n, p ∈ P i)
  have hdiv : ∀ n ∈ S, p ∣ n := by
    intro n hn
    obtain ⟨hcol, hsupp⟩ := Finset.mem_filter.mp hn
    exact hfactor n hcol hsupp
  have hnorm : ∀ n ∈ S, qNat n ≤ D := by
    intro n hn
    exact hcolnorm n (Finset.mem_filter.mp hn).1
  have hcount := finite_divisible_count p hp S D hdiv hnorm
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p ^ 6))‖ ≤
        ∑ n ∈ S, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight p
    _ ≤ ∑ n ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (S.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat p + 1) : ℕ) := by exact_mod_cast hcount
end OAI.ActualEisensteinCubic
