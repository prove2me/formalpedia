-- Prove2me | solution 1 for NLDefined.theorem_iff_valid
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:20:06.502865+00:00
-- url     : https://prove2.me/submissions/5b7273c6-f14e-4a7e-9e68-5b0ec43629d1

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_sound_complete

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (a : Formula) : Theorem a ↔ Valid a :=
  sound_complete (fun _ => False) a
end NLDefined
