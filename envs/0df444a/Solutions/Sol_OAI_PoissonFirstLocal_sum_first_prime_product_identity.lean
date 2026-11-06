-- Prove2me | solution 1 for OAI.PoissonFirstLocal.sum_first_prime_product_identity
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:07:25.378251+00:00
-- url     : https://prove2.me/submissions/25e8c4c0-372c-423f-9e72-6e4b747a86df

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonFirstLocal_first_prime_product_identity

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
open OAI.PoissonFirstLocal
open scoped Classical
namespace OAI.PoissonFirstLocal
theorem _root_.solution
    (S P : Finset ℕ) (side : Bool)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (χ : (n : ℕ) → MulChar (ZMod n) ℂ)
    (hχ : ∀ n, χ n ^ 6 = 1) (a : ℕ → ℂ) :
    (∑ n ∈ S, a n *
      (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p (χ n))) =
    (∑ n ∈ S, a n *
      ((χ n ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
       mask n (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p))) := by
  apply Finset.sum_congr rfl
  intro n hn
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n (χ n) (hχ n)]
end OAI.PoissonFirstLocal
