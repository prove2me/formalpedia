-- Prove2me | solution 1 for N4Code.equivalent_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:31:35.206655+00:00
-- url     : https://prove2.me/submissions/c33f822d-ea11-48ba-b621-2798142ebc42

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_rowPermute_xor

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} {C₁ C₂ C₃ : Code n} (h12 : Equivalent C₁ C₂)
    (h23 : Equivalent C₂ C₃) : Equivalent C₁ C₃ := by
  rcases h12 with ⟨ρ₁, p₁, f₁, h₁⟩
  rcases h23 with ⟨ρ₂, p₂, f₂, h₂⟩
  refine ⟨ρ₂.trans ρ₁, p₁.trans p₂, fun t => f₁ t != f₂ (p₁ t), ?_⟩
  intro t
  have hp : (p₁.trans p₂) t = p₂ (p₁ t) := rfl
  rw [hp]
  rw [h₂ (p₁ t)]
  rw [h₁ t]
  exact rowPermute_xor (ρ₁ := ρ₁) (ρ₂ := ρ₂) (b₁ := f₁ t) (b₂ := f₂ (p₁ t)) (C₁ t)
end N4Code
