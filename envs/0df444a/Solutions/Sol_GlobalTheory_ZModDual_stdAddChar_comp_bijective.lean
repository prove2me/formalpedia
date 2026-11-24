-- Prove2me | solution 1 for GlobalTheory.ZModDual.stdAddChar_comp_bijective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:20:08.393632+00:00
-- url     : https://prove2.me/submissions/80827cea-f856-4a5d-ba61-fd9842d6b2c4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveDualAddChar
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardDualZmodModuleEqCard
import Theorems.Thm_GlobalTheory_StandardAdditiveCharacter_bijective_dual_addChar


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZModDual
namespace GlobalTheory.ZModDual
theorem _root_.solution (n : ℕ) [NeZero n] (A : Type) [AddCommGroup A]
    [Module (ZMod n) A] :
    Function.Bijective fun φ : Module.Dual (ZMod n) A =>
      ((ZMod.stdAddChar (N := n)).compAddMonoidHom φ.toAddMonoidHom : AddChar A ℂ) := by
  first
  | exact @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar
  | (apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StandardAdditiveCharacter.bijective_dual_addChar ..)
end GlobalTheory.ZModDual
