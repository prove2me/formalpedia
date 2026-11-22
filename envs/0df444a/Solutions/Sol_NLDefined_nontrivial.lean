-- Prove2me | solution 1 for NLDefined.nontrivial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:05.558914+00:00
-- url     : https://prove2.me/submissions/7ded1e1b-852a-4fd2-ab54-d298f26c9fc4

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_sound

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution : ¬ Theorem (Formula.var 0) := by
  intro h
  have hv := sound h V sixMatrix (fun _ => V.b)
    (by intro b hb; exact False.elim hb)
  change (false : Bool) = true at hv
  cases hv
end NLDefined
