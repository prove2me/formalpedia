-- Prove2me | solution 1 for NLPrimitive.sound_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:56.353826+00:00
-- url     : https://prove2.me/submissions/abc2655b-24c6-4e1f-bd0b-489552e1a021

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_sound
import Theorems.Thm_NLPrimitive_complete

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution (Γ : Formula → Prop) (a : Formula) :
    Derives Γ a ↔ Entails Γ a :=
  ⟨sound, complete⟩
end NLPrimitive
