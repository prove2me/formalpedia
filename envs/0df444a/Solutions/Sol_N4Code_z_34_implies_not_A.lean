-- Prove2me | solution 1 for N4Code.z_34_implies_not_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:20:24.735438+00:00
-- url     : https://prove2.me/submissions/368931b7-13d3-4a08-bd91-4bb9d5e5c276

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (C : Code n) (t₁ t₂ : Fin n) (y : Word n) :
    (Z3 C t₁ t₂ y ∨ Z4 C t₁ t₂ y) → ¬ (Z1 C t₁ t₂ y ∨ Z2 C t₁ t₂ y ∨ Z5 C t₁ t₂ y) := by
  rintro hz (h1 | h2 | h5)
  · rcases hz with hz | hz
    · exact hz.1 h1
    · exact hz.1 h1
  · rcases hz with hz | hz
    · exact (not_lt_of_ge h2.2) hz.2.1
    · exact (not_lt_of_ge h2.2) hz.2.1
  · rcases hz with hz | hz
    · exact (not_lt_of_ge hz.2.2) h5.2.2.1
    · exact (not_lt_of_ge h5.2.2.2) hz.2.2.2
end N4Code
