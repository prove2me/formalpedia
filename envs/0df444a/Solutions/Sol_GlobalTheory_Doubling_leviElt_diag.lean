-- Prove2me | solution 1 for GlobalTheory.Doubling.leviElt_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:06:15.09948+00:00
-- url     : https://prove2.me/submissions/c05531af-0a51-4969-a160-68c67ec5dcb1

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct
import Theorems.Thm_GlobalTheory_Doubling_leviElt_mulVec
import Theorems.Thm_GlobalTheory_Doubling_flatSec_self
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Doubling.flatSec_self



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable (e : n ⊕ n ≃ ι) [Fintype n] [Fintype ι] [DecidableEq n] [DecidableEq ι]
variable [Invertible (2 : A)]
namespace GlobalTheory.Doubling
theorem _root_.solution (g : GL n A × GL n A) (x : n → A) :
    (leviElt e g).1 *ᵥ pairVec e x x = pairVec e (g.1.1 *ᵥ x) (g.1.1 *ᵥ x) := by
  simpa using leviElt_mulVec e g x 0
end GlobalTheory.Doubling
