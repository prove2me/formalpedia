-- Prove2me | solution 1 for OAI.PoissonFirstLocal.first_prime_product_with_b0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:44.661276+00:00
-- url     : https://prove2.me/submissions/10df3ef1-6a41-41f0-a60d-4993ca0017f5

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
import Theorems.Thm_OAI_PoissonFirstLocal_first_prime_product_identity
import Theorems.Thm_OAI_PoissonFirstLocal_mask_redundant_overlap

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
    (side : Bool) (P : Finset ℕ)
    (parityBit ε₁ ε₂ : ℕ → Bool)
    (n b₀ m : ℕ) (χ : MulChar (ZMod n) ℂ) (hχ : χ ^ 6 = 1)
    (hB : (∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) ∣ b₀)
    (hb : b₀ ∣
      ((∏ p ∈ P with ¬retained (parityBit p) (ε₁ p) (ε₂ p), p) *
       (∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p)) ^ m) :
    (∏ p ∈ P, oldFactor side (parityBit p) (ε₁ p) (ε₂ p) n p χ) =
      (χ ((∏ p ∈ P with retained (parityBit p) (ε₁ p) (ε₂ p), p : ℕ) : ZMod n)) ^ 4 *
      mask n b₀ := by
  rw [first_prime_product_identity side P parityBit ε₁ ε₂ n χ hχ]
  exact mask_redundant_overlap n _ _ b₀ m χ hB hb
end OAI.PoissonFirstLocal
