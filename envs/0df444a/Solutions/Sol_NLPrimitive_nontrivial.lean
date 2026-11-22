-- Prove2me | solution 1 for NLPrimitive.nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:15.316912+00:00
-- url     : https://prove2.me/submissions/7d979c52-4f8e-4ee3-b05f-2d5073ae158c

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_sound

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution : ¬ Theorem (Formula.var 0) := by
  intro h
  have hv := sound h Bool boolMatrix (fun _ => false)
    (by intro b hb; exact False.elim hb)
  change (false : Bool) = true at hv
  cases hv
end NLPrimitive
