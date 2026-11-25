-- Prove2me | solution 1 for GlobalTheory.FinWeil.quot_mk_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:49:22.215533+00:00
-- url     : https://prove2.me/submissions/e830d78e-f0b0-4319-8b51-f403217ea46e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsHeisTrivial
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SumOpTransversal

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Classical GlobalTheory.FinWeil
open scoped BigOperators
open GlobalTheory GlobalTheory.FinWeil
variable {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M]
namespace GlobalTheory.FinWeil
theorem _root_.solution (A B : Submodule R X) (x y : B.toAddSubgroup) :
    (QuotientAddGroup.mk x : B.toAddSubgroup ⧸ A.toAddSubgroup.addSubgroupOf B.toAddSubgroup) = QuotientAddGroup.mk y ↔
      (y : X) - x ∈ A := by
  rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
  have : ((-x + y : B.toAddSubgroup) : X) = (y : X) - x := by
    push_cast; abel
  rw [this]; rfl
end GlobalTheory.FinWeil
