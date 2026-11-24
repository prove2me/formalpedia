-- Prove2me | solution 1 for GlobalTheory.SepPoint.exists_common_mul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T20:44:37.344072+00:00
-- url     : https://prove2.me/submissions/b274dbf5-017c-4395-a2a1-19d77615f0c9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsIntegrallyClosedAdjoin
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPrimitiveElementSeparabilityCertificate

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open scoped IntermediateField.algebraAdjoinAdjoin
open GlobalTheory GlobalTheory.SepPoint
namespace GlobalTheory.SepPoint
theorem _root_.solution {k F : Type} [Field k] [Field F] [Algebra k F]
    (R S : Subalgebra k F) (hRS : R ≤ S) (T : Finset F)
    (h : ∀ x ∈ T, ∃ b : R, b ≠ 0 ∧ (b : F) * x ∈ S) :
    ∃ B : R, B ≠ 0 ∧ ∀ x ∈ T, (B : F) * x ∈ S := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | insert a T ha ih =>
    obtain ⟨B, hB, hBT⟩ := ih fun x hx => h x (Finset.mem_insert_of_mem hx)
    obtain ⟨b, hb, hba⟩ := h a (Finset.mem_insert_self a T)
    refine ⟨b * B, mul_ne_zero hb hB, fun x hx => ?_⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · have : ((b * B : R) : F) * x = (B : F) * ((b : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS B.2) hba
    · have : ((b * B : R) : F) * x = (b : F) * ((B : F) * x) := by push_cast; ring
      rw [this]; exact S.mul_mem (hRS b.2) (hBT x hx)
end GlobalTheory.SepPoint
