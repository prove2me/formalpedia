-- Prove2me | solution 1 for NLDefined.sound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T19:18:37.516998+00:00
-- url     : https://prove2.me/submissions/9a154224-febe-4739-8fbe-47cedba88ecb

import Std
import Definitions.Def_NLDefined
import Theorems.Thm_NLDefined_axiom_sound

set_option autoImplicit true
set_option autoImplicit false
open NLDefined
namespace NLDefined
theorem _root_.solution {Γ : Formula → Prop} {a : Formula}
    (h : Derives Γ a) : Entails Γ a := by
  intro α M v hΓ
  induction h with
  | hyp hb => exact hΓ _ hb
  | ax hb => exact axiom_sound M v hb
  | mp ha hab iha ihab => exact M.mp _ _ iha ihab
  | adj ha hb iha ihb => exact M.adj _ _ iha ihb
end NLDefined
