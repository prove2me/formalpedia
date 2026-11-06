-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.rational_sixth_row_approx_two_factors
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:48:17.790204+00:00
-- url     : https://prove2.me/submissions/eba02aab-77d0-4a94-9a6e-6d5f4271d005

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_difference_norm
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_ShortDraftLatticeCount_finite_divisible_count
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
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ) (r a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (D : ℕ)
    (hfactor : ∀ n ∈ columns,
      (∃ i ∈ support n, r ∈ P i) → a ∣ n ∨ b ∣ n)
    (hcolnorm : ∀ n ∈ columns, qNat n ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1) :
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
      (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
  classical
  let Bad := columns.filter (fun n => ∃ i ∈ support n, r ∈ P i)
  let Sa := columns.filter (fun n => a ∣ n)
  let Sb := columns.filter (fun n => b ∣ n)
  have hsub : Bad ⊆ Sa ∪ Sb := by
    intro n hn
    obtain ⟨hcol, hbad⟩ := Finset.mem_filter.mp hn
    rcases hfactor n hcol hbad with hna | hnb
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hcol, hna⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hcol, hnb⟩)
  have hSa : Sa.card ≤ 64 * (D / qNat a + 1) :=
    finite_divisible_count a ha Sa D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hSb : Sb.card ≤ 64 * (D / qNat b + 1) :=
    finite_divisible_count b hb Sb D
      (by intro n hn; exact (Finset.mem_filter.mp hn).2)
      (by intro n hn; exact hcolnorm n (Finset.mem_filter.mp hn).1)
  have hcard : Bad.card ≤
      64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) := by
    calc
      Bad.card ≤ (Sa ∪ Sb).card := Finset.card_le_card hsub
      _ ≤ Sa.card + Sb.card := Finset.card_union_le Sa Sb
      _ ≤ 64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) :=
        Nat.add_le_add hSa hSb
  calc
    ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (r ^ 6))‖ ≤
        ∑ n ∈ Bad, ‖weight n‖ :=
      finiteSquarefreeRow_difference_norm P hgood columns support weight r
    _ ≤ ∑ n ∈ Bad, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      exact hweight n (Finset.mem_filter.mp hn).1
    _ = (Bad.card : ℝ) := by simp
    _ ≤ (64 * (D / qNat a + 1) + 64 * (D / qNat b + 1) : ℕ) := by
      exact_mod_cast hcard
end OAI.ActualEisensteinCubic
