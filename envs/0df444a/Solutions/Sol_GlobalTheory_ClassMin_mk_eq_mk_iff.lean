-- Prove2me | solution 1 for GlobalTheory.ClassMin.mk_eq_mk_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:30:38.10687+00:00
-- url     : https://prove2.me/submissions/ce0bf8a8-ced2-4898-9b5d-3e2ac1bcae84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsReducedBasisOfLinearIndependent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsShiftedLtClassMin
import Theorems.Thm_GlobalTheory_IsSiegel_mk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Module
open scoped Pointwise
variable {X : Type*} [AddCommGroup X]
namespace GlobalTheory.ClassMin
theorem _root_.solution (N : ℤ) (a b : X) :
    (Submodule.Quotient.mk b : QuotSMulTop N X) = Submodule.Quotient.mk a ↔ ∃ w, b = a + N • w := by
  rw [Submodule.Quotient.eq, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨w, _, h⟩ => ⟨w, by rw [h]; abel⟩, fun ⟨w, h⟩ => ⟨w, trivial, by rw [h]; abel⟩⟩
end GlobalTheory.ClassMin
