-- Prove2me | solution 1 for LongGapsBetweenPrimes.productKernel_symm
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:47.410435+00:00
-- url     : https://prove2.me/submissions/36bf1d1c-5fb4-45bf-a8fa-135e9a11dcf3

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_localKernel_symm

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ τ : α → Option (Fin k)) : productKernel size σ τ = productKernel size τ σ := by
  exact Finset.prod_congr rfl fun p _ => localKernel_symm (size p) (σ p) (τ p)
end LongGapsBetweenPrimes
