-- Prove2me | solution 1 for NLPrimitive.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:48.33993+00:00
-- url     : https://prove2.me/submissions/eb6733f7-8af5-4225-a271-2716224308a8

import Std
import Definitions.Def_NLPrimitive
import Theorems.Thm_NLPrimitive_axiom_sound

set_option autoImplicit true
set_option autoImplicit false
open NLPrimitive
namespace NLPrimitive
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : Derives Γ a) : Entails Γ a := by
  intro α M v hΓ
  induction h with
  | hyp hb => exact hΓ _ hb
  | ax hb => exact axiom_sound M v hb
  | mp ha hab iha ihab => exact M.mp _ _ iha ihab
  | adj ha hb iha ihb => exact M.adj _ _ iha ihb
end NLPrimitive
