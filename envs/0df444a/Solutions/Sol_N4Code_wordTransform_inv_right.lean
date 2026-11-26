-- Prove2me | solution 1 for N4Code.wordTransform_inv_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:01:16.323577+00:00
-- url     : https://prove2.me/submissions/29f243a1-954d-4e6b-b022-226d74016330

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) (y : Word n) :
    wordTransformInv p f (wordTransform p f y) = y := by
  funext t
  cases hf : f (p.symm t) <;> simp [wordTransform, wordTransformInv, hf]
end N4Code
