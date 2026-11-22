-- Prove2me | solution 1 for NLDefined.sound_complete
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:19:41.935224+00:00
-- url     : https://prove2.me/submissions/8c4451f2-0c22-4f93-8825-f522127d1b01

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_sound
import Theorems.Thm_NLDefined_complete

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution (Γ : Formula → Prop) (a : Formula) :
    Derives Γ a ↔ Entails Γ a :=
  ⟨sound, complete⟩
end NLDefined
