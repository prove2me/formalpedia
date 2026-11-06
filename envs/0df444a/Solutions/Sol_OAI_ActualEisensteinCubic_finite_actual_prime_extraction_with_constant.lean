-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finite_actual_prime_extraction_with_constant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:29:05.406719+00:00
-- url     : https://prove2.me/submissions/ee80db78-a987-47f6-a172-7724c1633e41

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticNormalization
import Theorems.Thm_OAI_PowerExtraction_from_finite_sixth_power_rows_with_constant
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_one
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_sixth_row_approx_ideal_norm
import Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_injective
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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O) (rows : Finset O)
    (D : ℕ) (ε C : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hC : 1 ≤ C)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hrows : selected.image (fun i => p i ^ 6) ⊆ rows)
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hrowbound : ∀ i ∈ selected,
      ((64 * (D / Ideal.absNorm (Ideal.span {p i}) + 1) : ℕ) : ℝ) ≤
        C * (D : ℝ) ^ (49 / 60 : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤ (selected.card : ℝ))
    (hmean :
      (∑ u ∈ rows,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * C * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤ C * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (hrowbound i hi)
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hbound := PowerExtraction.from_finite_sixth_power_rows_with_constant
    rows selected (fun i => p i ^ 6) A 1 (D : ℝ) ε C
    (by exact_mod_cast hD) hε hC hrows hinjRows happrox hcount hmean'
  simpa only [hone] using hbound
end OAI.ActualEisensteinCubic
