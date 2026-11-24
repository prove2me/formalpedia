-- Prove2me | solution 1 for GlobalTheory.Doubling.coe_ioU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:24:54.754886+00:00
-- url     : https://prove2.me/submissions/5a323f15-b967-4745-9b4e-8638756a1fe2

import Mathlib
import Definitions.Def_Formalism_SatakeDualWeyl_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_IsIwasawaOfIsCompact
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_MemSiegelOfIffRightAct

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Doubling
open Matrix Formalism.UG
variable {A B : Type} [CommRing A] [CommRing B] {m n ι : Type}
variable [Fintype m] [Fintype n] [Fintype ι] [DecidableEq m] [DecidableEq n] [DecidableEq ι] (σ : A →+* A)
namespace GlobalTheory.Doubling
theorem _root_.solution (e : n ⊕ n ≃ ι) {J : Matrix n n A} {Q : Matrix ι ι A} (h : Q = dblGram e J) (g : UJ σ J × UJ σ J) :
    (ioU σ e h g : GL ι A) = blkGL e (g.1, g.2) := rfl
end GlobalTheory.Doubling
