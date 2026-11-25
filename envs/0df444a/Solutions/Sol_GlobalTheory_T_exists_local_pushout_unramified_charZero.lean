-- Prove2me | solution 1 for GlobalTheory.T.exists_local_pushout_unramified_charZero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T18:19:48.011552+00:00
-- url     : https://prove2.me/submissions/cdfa879e-62e8-4678-a1de-2c2a3996dd5a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_EqZeroOfForallLTensorEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLocalPushoutUnramifiedCharZeroStatement
import Theorems.Thm_GlobalTheory_UnramPushout_exists_local_pushout


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A V V' : Type) [CommRing A] [CommRing V] [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (f : A →+* V) (f' : A →+* V'), f'.Flat → (maximalIdeal V).comap f = (maximalIdeal V').comap f' → ((maximalIdeal V).comap f).map f = maximalIdeal V → ((maximalIdeal V').comap f').map f' = maximalIdeal V' → CharZero (ResidueField V) → ∃ (B : Type) (_ : CommRing B) (_ : IsLocalRing B) (g : V →+* B) (g' : V' →+* B), g.comp f = g'.comp f' ∧ g.Flat ∧ (maximalIdeal V).map g = maximalIdeal B ∧ (maximalIdeal V').map g' = maximalIdeal B := by
  first | exact @GlobalTheory.UnramPushout.exists_local_pushout | exact GlobalTheory.UnramPushout.exists_local_pushout | (intros; apply GlobalTheory.UnramPushout.exists_local_pushout <;> assumption)
end _root_.GlobalTheory.T
