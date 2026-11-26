-- Prove2me | solution 1 for N4Code.flipTwoBits_involutive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:18:03.708514+00:00
-- url     : https://prove2.me/submissions/d80b9786-7a6c-4849-acc9-66b393ebdac3

import Definitions.Def_N4Code_ZeroColumn
import Definitions.Def_N4Code_TwoColumn

set_option autoImplicit true
open N4Code
set_option maxRecDepth 1000000
open scoped BigOperators
namespace N4Code
theorem _root_.solution {n : ℕ} (t₁ t₂ : Fin n) (y : Word n) :
    flipTwoBits t₁ t₂ (flipTwoBits t₁ t₂ y) = y := by
  funext u
  by_cases h : u = t₁ ∨ u = t₂ <;> simp [flipTwoBits, h]
end N4Code
