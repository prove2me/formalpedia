-- Prove2me | solution 1 for GlobalTheory.CharFlag.subRep_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T02:29:59.093992+00:00
-- url     : https://prove2.me/submissions/b4b20ea4-413f-49b3-a37a-0b85025d6fdd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SubRepApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CharFlag
variable {k Γ V : Type} [Field k] [Group Γ] [AddCommGroup V] [Module k V]
namespace GlobalTheory.CharFlag
theorem _root_.solution (π : Representation k Γ V) (S : Submodule k V) (hS : Stab π S) (g : Γ) (x : S) :
    ((subRep π S hS g x : S) : V) = π g x := rfl
end GlobalTheory.CharFlag
