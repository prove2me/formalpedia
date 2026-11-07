-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.eventual_finite_extraction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T06:29:58.639192+00:00
-- url     : https://prove2.me/submissions/01a7ea6c-1566-4223-9632-53017e608a0f

import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_OscillatoryGaussian
import Definitions.Def_OAI_NumberTheory_DirichletL_PrimeRows_RationalApproximation
import Theorems.Thm_OAI_RationalQuant_from_rational_prime_rows_with_constant
import Theorems.Thm_OAI_RationalPrimeExtraction_eventual_count_power
import Theorems.Thm_OAI_RationalPrimeExtraction_selected_rows_in_ball
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_sixth_injective
import Theorems.Thm_OAI_IdealGaussCRT_traceProdChar_mk
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
open ActualEisensteinCubic
open Filter
open ActualEisensteinCubic RationalPrimeExtraction ShortDraftLatticeCount
open ActualEisensteinCubic ShortDraftLatticeCount
open OAI.RationalPrimeExtraction
namespace OAI.RationalPrimeExtraction
theorem _root_.solution (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℝ, ∀ D : ℕ, D₀ ≤ (D : ℝ) →
      ∀ A : O → ℂ,
      (∀ r ∈ selected ((D : ℝ) ^ (4 / 45 : ℝ)),
        ‖A 1 - A ((r : O) ^ 6)‖ ≤
          512 * (D : ℝ) ^ (41 / 45 : ℝ)) →
      (∑ u ∈ rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊,
        ‖A u‖ ^ 2) ≤
          (D : ℝ) ^ ((31 / 15 : ℝ) + ε) →
      ‖A 1‖ ≤ 1024 * (D : ℝ) ^ ((89 / 90 : ℝ) + ε) := by
  obtain ⟨D₀, hcount⟩ := eventual_count_power ε hε
  refine ⟨D₀, ?_⟩
  intro D hD A happrox hmean
  classical
  obtain ⟨hDtwo, hJcount⟩ := hcount D hD
  have hDone : 1 ≤ D := by omega
  have hDreal : (1 : ℝ) ≤ D := by exact_mod_cast hDone
  have hDpos : (0 : ℝ) < D := lt_of_lt_of_le zero_lt_one hDreal
  let S := selected ((D : ℝ) ^ (4 / 45 : ℝ))
  let rows := rowNormBall ⌈(D : ℝ) ^ (16 / 15 : ℝ)⌉₊
  let E : ℝ := 512 * (D : ℝ) ^ (41 / 45 : ℝ)
  let M : ℝ := (D : ℝ) ^ ((31 / 15 : ℝ) + ε)
  have hrows : S.image (fun r : ℕ => (r : O) ^ 6) ⊆ rows :=
    selected_rows_in_ball D hDone
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6) (S : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hextract := ShortDraft.complex_row_extraction rows S
    (fun r : ℕ => (r : O) ^ 6) A 1 E M
    (by dsimp [E]; positivity) hrows hinj happrox hmean
  have herr : E ^ 2 = 512 ^ 2 * (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [E]
    rw [mul_pow]
    congr 1
    calc
      ((D : ℝ) ^ (41 / 45 : ℝ)) ^ 2 =
          (D : ℝ) ^ ((41 / 45 : ℝ) * (2 : ℕ)) :=
          (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = (D : ℝ) ^ (82 / 45 : ℝ) := by congr 1; norm_num
  rw [herr] at hextract
  have hextract' : (S.card : ℝ) * ‖A 1‖ ^ 2 ≤
      2 * (D : ℝ) ^ ((31 / 15 : ℝ) + ε) +
      2 * (S.card : ℝ) * 512 ^ 2 *
        (D : ℝ) ^ (82 / 45 : ℝ) := by
    dsimp [M] at hextract
    nlinarith [hextract]
  have hbound := RationalQuant.from_rational_prime_rows_with_constant
    (D : ℝ) ε (S.card : ℝ) ‖A 1‖ 512 hDreal hε.le
    (norm_nonneg _) (by norm_num) hJcount hextract'
  simpa only [show (2 : ℝ) * 512 = 1024 by norm_num] using hbound
end OAI.RationalPrimeExtraction
