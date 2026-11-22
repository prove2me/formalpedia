-- Prove2me | solution 1 for NLPrimitive.theorem_iff_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:29.938843+00:00
-- url     : https://prove2.me/submissions/ad29ff44-3a41-4ce2-adef-191a6367eae5

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_sound_complete

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution (a : Formula) : Theorem a ↔ Valid a :=
  sound_complete (fun _ => False) a
end NLPrimitive
