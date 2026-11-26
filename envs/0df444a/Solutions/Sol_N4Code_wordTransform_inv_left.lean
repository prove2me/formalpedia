-- Prove2me | solution 1 for N4Code.wordTransform_inv_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:58:58.838346+00:00
-- url     : https://prove2.me/submissions/21036c70-fbb5-4ee0-82eb-af6eb7729020

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
    wordTransform p f (wordTransformInv p f y) = y := by
  funext t
  cases hf : f t <;> simp [wordTransform, wordTransformInv, hf]
end N4Code
