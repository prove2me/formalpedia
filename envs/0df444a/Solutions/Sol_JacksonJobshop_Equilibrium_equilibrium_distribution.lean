-- Prove2me | solution 1 for JacksonJobshop.Equilibrium.equilibrium_distribution
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-19T03:38:39.095219+00:00
-- url     : https://prove2.me/submissions/1fa0846f-1195-49c0-83a6-8e0443c5dcb7

import Mathlib
import Definitions.Def_JacksonJobshop_Equilibrium_System
import Theorems.Thm_JacksonJobshop_Equilibrium_product_form_is_distribution
import Theorems.Thm_JacksonJobshop_Equilibrium_product_form_satisfies_balance
import Theorems.Thm_JacksonJobshop_Equilibrium_equilibrium_unique

set_option autoImplicit false

open JacksonJobshop.Equilibrium in
theorem solution {N : ℕ} (sys : JobshopSystem N) (hπ : 0 < piConst sys) :
    IsEquilibrium sys (productForm sys) ∧
    ((∃ Λ : ℝ, ∀ K, sys.lam K ≤ Λ) →
      ∀ q : (Fin N → ℕ) → ℝ, IsEquilibrium sys q → q = productForm sys) := by
  obtain ⟨hnn, hsum⟩ := product_form_is_distribution sys hπ
  have hbal := product_form_satisfies_balance sys
  have heq : IsEquilibrium sys (productForm sys) := ⟨hnn, hsum, hbal⟩
  exact ⟨heq, fun hbdd q hq => equilibrium_unique sys hbdd q (productForm sys) hq heq⟩
