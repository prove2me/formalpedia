-- Prove2me | solution 1 for OAI.PowerExtraction.from_finite_sixth_power_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T05:15:04.353206+00:00
-- url     : https://prove2.me/submissions/7073438c-37ec-4913-bd78-e219375965dd

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
import Theorems.Thm_OAI_PowerExtraction_from_mean_square_and_prime_rows
import Theorems.Thm_OAI_ShortDraft_complex_row_extraction


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
open OAI.PowerExtraction
namespace OAI.PowerExtraction
theorem _root_.solution
    {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (D ε : ℝ)
    (hD : 1 ≤ D) (hε : 0 ≤ ε)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes,
      ‖A untwisted - A (row p)‖ ≤ D ^ (49 / 60 : ℝ))
    (hcount : D ^ ((11 / 60 : ℝ) - ε) ≤ (primes.card : ℝ))
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤
      D ^ ((21 / 10 : ℝ) + ε)) :
    ‖A untwisted‖ ≤ 2 * D ^ ((23 / 24 : ℝ) + ε) := by
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD
  have hextract := ShortDraft.complex_row_extraction rows primes row A untwisted
    (D ^ (49 / 60 : ℝ)) (D ^ ((21 / 10 : ℝ) + ε))
    (by positivity) hrows hinj happrox hmean
  have herror : (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ (49 / 30 : ℝ) := by
    calc
      (D ^ (49 / 60 : ℝ)) ^ 2 = D ^ ((49 / 60 : ℝ) * 2) :=
        (Real.rpow_mul_natCast hDpos.le _ 2).symm
      _ = D ^ (49 / 30 : ℝ) := by congr 1; norm_num
  rw [herror] at hextract
  exact from_mean_square_and_prime_rows D ε (primes.card : ℝ)
    ‖A untwisted‖ hD hε (norm_nonneg _) hcount hextract
end OAI.PowerExtraction
