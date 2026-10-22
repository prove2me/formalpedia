-- Prove2me | solution 1 for InventoryBounds.minimizer_value_error
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:32:17.726039+00:00
-- url     : https://prove2.me/submissions/487c3a4b-3c03-4226-8faf-277a3fd3bfd1

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
set_option autoImplicit false

theorem solution {α : Type*} (f fhat : α → ℝ)
    (s shat : α) (b : ℝ)
    (hdev : ∀ a, |f a - fhat a| ≤ b)
    (htrue : ∀ a, f s ≤ f a)
    (hemp : ∀ a, fhat shat ≤ fhat a) :
    |fhat shat - f s| ≤ b := by
  have h1 := abs_le.mp (hdev shat)
  have h2 := abs_le.mp (hdev s)
  have h3 := htrue shat
  have h4 := hemp s
  rw [abs_le]
  constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
