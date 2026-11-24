-- Prove2me | solution 1 for GlobalTheory.Doubling.leviElt_anti
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T15:06:14.912204+00:00
-- url     : https://prove2.me/submissions/48ee150f-4bd7-4a1e-a29a-544466255fba

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
theorem _root_.solution (g : GL n A × GL n A) (y : n → A) :
    (leviElt e g).1 *ᵥ pairVec e y (-y) = pairVec e (g.2.1 *ᵥ y) (-(g.2.1 *ᵥ y)) := by
  simpa using leviElt_mulVec e g 0 y
end GlobalTheory.Doubling
