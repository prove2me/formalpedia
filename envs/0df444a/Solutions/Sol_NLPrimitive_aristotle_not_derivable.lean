-- Prove2me | solution 1 for NLPrimitive.aristotle_not_derivable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:13.910547+00:00
-- url     : https://prove2.me/submissions/fb5fa5c3-534e-40e2-82cc-663a05093531

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_sound

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution : ¬ Theorem aristotle := by
  intro h
  have hv := sound h Bool boolMatrix (fun _ => false)
    (by intro b hb; exact False.elim hb)
  change (false : Bool) = true at hv
  cases hv
end NLPrimitive
