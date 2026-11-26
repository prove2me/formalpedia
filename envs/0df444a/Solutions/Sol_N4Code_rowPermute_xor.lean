-- Prove2me | solution 1 for N4Code.rowPermute_xor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:25:03.254399+00:00
-- url     : https://prove2.me/submissions/12c8fefa-df7d-40a8-9035-52d801e2bf70

import Definitions.Def_N4Code_Compare
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_ZeroColumn
import Theorems.Thm_N4Code_rowPermute_comp
import Theorems.Thm_N4Code_flipCol_involutive
import Theorems.Thm_N4Code_rowPermute_flipCol

set_option autoImplicit true
open scoped BigOperators
noncomputable section
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {ρ₁ ρ₂ : Equiv (Fin 4) (Fin 4)} (b₁ b₂ : Bool) (c : Column) :
    rowPermute ρ₂ (if b₂ = true then flipCol (rowPermute ρ₁ (if b₁ = true then flipCol c else c))
        else rowPermute ρ₁ (if b₁ = true then flipCol c else c)) =
      rowPermute (ρ₂.trans ρ₁) (if (b₁ != b₂) = true then flipCol c else c) := by
  by_cases h1 : b₁ = true <;> by_cases h2 : b₂ = true <;>
    simp [h1, h2, rowPermute_flipCol, rowPermute_comp, flipCol_involutive]
end N4Code
