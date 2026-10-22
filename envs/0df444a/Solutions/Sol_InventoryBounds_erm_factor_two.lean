-- Prove2me | solution 1 for InventoryBounds.erm_factor_two
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T16:29:18.752706+00:00
-- url     : https://prove2.me/submissions/f81b38d4-1c36-45c3-bb47-2911fc523d93

import Mathlib
import Definitions.Def_InventoryBounds_Primitives
set_option autoImplicit false

theorem solution {α : Type*} (f fhat : α → ℝ)
    (s shat : α) (b : ℝ)
    (hdev : ∀ a, |f a - fhat a| ≤ b)
    (hemp : fhat shat ≤ fhat s) :
    f shat - f s ≤ 2 * b := by
  have h1 := abs_le.mp (hdev shat)
  have h2 := abs_le.mp (hdev s)
  linarith [h1.2, h2.1]
