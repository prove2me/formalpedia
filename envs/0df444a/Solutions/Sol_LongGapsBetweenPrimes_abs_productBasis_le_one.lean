-- Prove2me | solution 1 for LongGapsBetweenPrimes.abs_productBasis_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:04:53.47616+00:00
-- url     : https://prove2.me/submissions/e916074b-78f6-4d39-b737-ad0fa26ef507

import Mathlib
import Definitions.Def_LongGapsBetweenPrimes

set_option autoImplicit true
open LongGapsBetweenPrimes
noncomputable section
namespace LongGapsBetweenPrimes
theorem _root_.solution {α : Type*} [Fintype α] {Ω J : α → Type*}
    (f : (p : α) → J p → Ω p → ℝ) (hf : ∀ p i t, |f p i t| ≤ 1)
    (σ : (p : α) → J p) (t : (p : α) → Ω p) : |productBasis f σ t| ≤ 1 := by
  rw [productBasis, Finset.abs_prod]
  exact Finset.prod_le_one (fun _ _ => abs_nonneg _) (fun p _ => hf p _ _)
end LongGapsBetweenPrimes
