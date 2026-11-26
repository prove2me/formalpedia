-- Prove2me | solution 1 for N4Code.bool_ne_cases
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:04.264853+00:00
-- url     : https://prove2.me/submissions/f6daf24c-6b20-4585-9637-114da57c2206

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {a b : Bool} (h : a ≠ b) :
    (a = true ∧ b = false) ∨ (a = false ∧ b = true) := by
  cases a <;> cases b
  · exfalso
    exact h rfl
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩
  · exfalso
    exact h rfl
end N4Code
