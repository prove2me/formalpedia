-- Prove2me | solution 1 for LongGapsBetweenPrimes.productKernel_diag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:50.105798+00:00
-- url     : https://prove2.me/submissions/60a171c2-32f0-4436-9a59-f419b028ab64

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes
import Theorems.Thm_LongGapsBetweenPrimes_localKernel_diag

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] (size : α → ℕ) {k : ℕ}
    (σ : α → Option (Fin k)) : productKernel size σ σ = 1 := by
  simp [productKernel, localKernel_diag]
end LongGapsBetweenPrimes
