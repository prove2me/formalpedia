-- Prove2me | solution 1 for N4Code.z_not_A_implies_34
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:28.561804+00:00
-- url     : https://prove2.me/submissions/039036f3-a9e0-4205-8b07-d70ad63d5a67

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn
import Theorems.Thm_N4Code_z_partition

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) → (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) := by
  intro hnot
  rcases z_partition C C t₁ t₂ y with ⟨i, hi, _⟩
  fin_cases i
  · exfalso
    exact hnot (Or.inl (by simpa [ZSet] using hi))
  · exfalso
    exact hnot (Or.inr (Or.inl (by simpa [ZSet] using hi)))
  · exact Or.inl (by simpa [ZSet] using hi)
  · exact Or.inr (by simpa [ZSet] using hi)
  · exfalso
    exact hnot (Or.inr (Or.inr (by simpa [ZSet] using hi)))
end N4Code
