-- Prove2me | solution 1 for N4Code.wordTransform_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:02:04.14161+00:00
-- url     : https://prove2.me/submissions/b032a1c2-1788-453d-9508-08f2175d99f4

import Definitions.Def_N4Code_Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Positivity
import Definitions.Def_N4Code_Performance
import Theorems.Thm_N4Code_wordTransform_inv_left
import Theorems.Thm_N4Code_wordTransform_inv_right

set_option autoImplicit true
open scoped BigOperators
open N4Code
set_option maxRecDepth 1000000
namespace N4Code
theorem _root_.solution {n : ℕ} (p : Equiv (Fin n) (Fin n)) (f : Fin n → Bool) :
    Function.Bijective (wordTransform p f) :=
  ⟨fun a b hab => by
    have h := congrArg (wordTransformInv p f) hab
    simpa [wordTransform_inv_right, wordTransform_inv_left] using h,
   fun y => ⟨wordTransformInv p f y, wordTransform_inv_left p f y⟩⟩
end N4Code
