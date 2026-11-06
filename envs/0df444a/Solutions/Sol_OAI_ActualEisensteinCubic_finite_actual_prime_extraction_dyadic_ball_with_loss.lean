-- Prove2me | solution 1 for OAI.ActualEisensteinCubic.finite_actual_prime_extraction_dyadic_ball_with_loss
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:50:19.116203+00:00
-- url     : https://prove2.me/submissions/93aaf0a1-2f96-4735-b9cb-885e4ae6a774

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianDualLimit
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Theorems.Thm_OAI_PowerExtraction_from_mean_square_and_prime_rows_with_loss
import Theorems.Thm_OAI_ActualEisensteinCubic_finiteSquarefreeRow_one
import Theorems.Thm_OAI_ActualEisensteinCubic_prime_sixth_row_approx_ideal_norm
import Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_in_rowNormBall
import Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_rows_injective
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
import Theorems.Thm_OAI_PowerExtraction_dyadic_prime_error_bound
import Theorems.Thm_OAI_ShortDraft_complex_row_extraction
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
namespace OAI.ActualEisensteinCubic
theorem _root_.solution
    {ι β : Type*} (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hgood : ∀ i, lambda ∉ P i)
    (columns : Finset O) (support : O → Finset ι) (weight : O → ℂ)
    (selected : Finset β) (p : β → O)
    (D H : ℕ) (ε M : ℝ) (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hM : 1 ≤ M)
    (hp : ∀ i ∈ selected, p i ≠ 0)
    (hprime : ∀ i ∈ selected, (Ideal.span {p i} : Ideal O).IsMaximal)
    (hinj : Set.InjOn (fun i => (Ideal.span {p i} : Ideal O)) (selected : Set β))
    (hsupport : ∀ n ∈ columns, ∀ i ∈ support n, n ∈ P i)
    (hcolnorm : ∀ n ∈ columns, Ideal.absNorm (Ideal.span {n}) ≤ D)
    (hweight : ∀ n ∈ columns, ‖weight n‖ ≤ 1)
    (hnormlower : ∀ i ∈ selected,
      (D : ℝ) ^ (11 / 60 : ℝ) / 2 ≤
        (Ideal.absNorm (Ideal.span {p i}) : ℝ))
    (hnormupper : ∀ i ∈ selected,
      (Ideal.absNorm (Ideal.span {p i}) : ℝ) ≤
        (D : ℝ) ^ (11 / 60 : ℝ))
    (hH : (D : ℝ) ^ (11 / 10 : ℝ) ≤ (H : ℝ))
    (hcount : (D : ℝ) ^ ((11 / 60 : ℝ) - ε) ≤
      M * (selected.card : ℝ))
    (hmean :
      (∑ u ∈ ShortDraftLatticeCount.rowNormBall H,
        ‖∑ n ∈ columns,
          weight n * finiteSquarefreeRow P hgood (support n) u‖ ^ 2) ≤
        M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε)) :
    ‖∑ n ∈ columns, weight n‖ ≤
      2 * (M + 192) * (D : ℝ) ^ ((23 / 24 : ℝ) + ε) := by
  classical
  let rows := ShortDraftLatticeCount.rowNormBall H
  let A : O → ℂ := fun u =>
    ∑ n ∈ columns, weight n * finiteSquarefreeRow P hgood (support n) u
  have hone : A 1 = ∑ n ∈ columns, weight n := by
    dsimp [A]
    apply Finset.sum_congr rfl
    intro n hn
    rw [finiteSquarefreeRow_one]
    ring
  have hrows : selected.image (fun i => p i ^ 6) ⊆ rows :=
    sixth_power_rows_in_rowNormBall selected p D H hD hnormupper hH
  have hinjRows : Set.InjOn (fun i => p i ^ 6) (selected : Set β) := by
    apply sixth_power_rows_injective selected
      (fun i => (Ideal.span {p i} : Ideal O)) p
    · exact hprime
    · intro i hi; rfl
    · exact hinj
  have happrox : ∀ i ∈ selected,
      ‖A 1 - A (p i ^ 6)‖ ≤
        192 * (D : ℝ) ^ (49 / 60 : ℝ) := by
    intro i hi
    rw [hone]
    change ‖(∑ n ∈ columns, weight n) -
      (∑ n ∈ columns,
        weight n * finiteSquarefreeRow P hgood (support n) (p i ^ 6))‖ ≤ _
    exact (prime_sixth_row_approx_ideal_norm P hgood columns support
      weight (p i) (hp i hi) (hprime i hi) D hsupport hcolnorm hweight).trans
      (PowerExtraction.dyadic_prime_error_bound D
        (Ideal.absNorm (Ideal.span {p i})) hD (hnormlower i hi))
  have hmean' : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε) := hmean
  have hextract := ShortDraft.complex_row_extraction rows selected
    (fun i => p i ^ 6) A 1
    (192 * (D : ℝ) ^ (49 / 60 : ℝ))
    (M * (D : ℝ) ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinjRows happrox hmean'
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  have hpow : ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      (D : ℝ) ^ (49 / 30 : ℝ) := by
    calc
      ((D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((49 / 60 : ℝ) * 2) :=
            (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (49 / 30 : ℝ) := by congr 1; norm_num
  have herror : (192 * (D : ℝ) ^ (49 / 60 : ℝ)) ^ 2 =
      192 ^ 2 * (D : ℝ) ^ (49 / 30 : ℝ) := by
    rw [mul_pow, hpow]
  rw [herror] at hextract
  have hbound := PowerExtraction.from_mean_square_and_prime_rows_with_loss
    (D : ℝ) ε (selected.card : ℝ) ‖A 1‖ 192 M hDreal hε
    (norm_nonneg _) (by norm_num) hM hcount
    (by simpa only [mul_assoc] using hextract)
  simpa only [hone] using hbound
end OAI.ActualEisensteinCubic
