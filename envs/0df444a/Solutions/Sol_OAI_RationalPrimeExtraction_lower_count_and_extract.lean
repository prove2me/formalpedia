-- Prove2me | solution 1 for OAI.RationalPrimeExtraction.lower_count_and_extract
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:49:52.430222+00:00
-- url     : https://prove2.me/submissions/fc960912-c8b3-45ba-8fc9-c5e6b045df1f

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
import Theorems.Thm_OAI_ActualEisensteinCubic_rational_sixth_injective
import Theorems.Thm_OAI_ShortDraft_complex_row_extraction
import Theorems.Thm_OAI_rational_prime_three_interval_count


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
open OAI.RationalPrimeExtraction
namespace OAI.RationalPrimeExtraction
theorem _root_.solution
    [DecidableEq O] (A : O → ℂ) (rows : Finset O) (E B : ℝ) (hE : 0 ≤ E) :
    ∃ Y₀ : ℝ, ∀ Y : ℝ, Y₀ ≤ Y →
      (selected Y).image (fun r : ℕ => (r : O) ^ 6) ⊆ rows →
      (∀ r ∈ selected Y, ‖A 1 - A ((r : O) ^ 6)‖ ≤ E) →
      (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ B →
      (Real.log 2 / 20) * (Y / Real.log Y) * ‖A 1‖ ^ 2 ≤
        2 * B + 2 * ((selected Y).card : ℝ) * E ^ 2 := by
  obtain ⟨Y₀, hcount⟩ := rational_prime_three_interval_count
  refine ⟨Y₀, ?_⟩
  intro Y hY hrows happrox hmean
  have hcard : (Real.log 2 / 20) * (Y / Real.log Y) ≤
      ((selected Y).card : ℝ) := hcount Y hY
  have hinj : Set.InjOn (fun r : ℕ => (r : O) ^ 6)
      ((selected Y : Finset ℕ) : Set ℕ) := by
    intro r _ s _ hrs
    exact rational_sixth_injective hrs
  have hmain := ShortDraft.complex_row_extraction rows (selected Y)
    (fun r : ℕ => (r : O) ^ 6) A 1 E B hE hrows hinj happrox hmean
  have hsquared : 0 ≤ ‖A 1‖ ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_right hcard hsquared).trans hmain
end OAI.RationalPrimeExtraction
