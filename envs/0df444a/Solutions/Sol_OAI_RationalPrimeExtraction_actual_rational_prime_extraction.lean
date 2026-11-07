-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.actual_rational_prime_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:31:08.806568+00:00
-- url     : https://prove2.me/submissions/a7da2bfe-5c19-4134-80f7-24251a96cadd

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_RationalPrimeExtraction_selected_row_error_bound
import Theorems.Thm_OAI_RationalPrimeExtraction_eventual_finite_extraction
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_one
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_prime_sixth_row_approx
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
open Filter Real Asymptotics
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.RationalPrimeExtraction
open ActualEisensteinCubic ShortDraftLatticeCount
namespace OAI.RationalPrimeExtraction
theorem _root_.solution
    {ι : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι)
    (weight : O → ℂ)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      (∀ n ∈ columns, qNat n ≤ D) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖∑ n ∈ columns, weight n‖ ≤
        1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₁, hgeneric⟩ := eventual_finite_extraction ε hε
  refine ⟨max 2 D₁, ?_⟩
  intro D hD hcolnorm hmean
  classical
  have hDtwoReal : (2 : ℝ) ≤ D := (le_max_left _ _).trans hD
  have hDtwo : 2 ≤ D := by exact_mod_cast hDtwoReal
  have hDone : 1 ≤ D := by omega
  have hDgeneric : D₁ ≤ (D : ℝ) := (le_max_right _ _).trans hD
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have happrox : ∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
      ‖A 1 - A ((r : O) ^ 6)‖ ≤
        512 * (D : ℝ) ^ (41 / 45 : ℝ) := by
    intro r hr
    have hrprime : r.Prime := (Finset.mem_filter.mp hr).2
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) ((r : O) ^ 6))‖ ≤ _
    exact (rational_prime_sixth_row_approx P hgood columns support weight
      r hrprime D hsupport hcolnorm hweight).trans
      (selected_row_error_bound D hDone r hr)
  have hmean' :
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤ (D : ℝ) ^ ((31 / 15 : ℝ) + ε) := hmean
  have hbound := hgeneric D hDgeneric A happrox hmean'
  simpa only [hone] using hbound
end OAI.RationalPrimeExtraction
