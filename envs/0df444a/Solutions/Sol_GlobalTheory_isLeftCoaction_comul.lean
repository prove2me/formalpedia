-- Prove2me | solution 1 for GlobalTheory.isLeftCoaction_comul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:25:58.929835+00:00
-- url     : https://prove2.me/submissions/e60164c7-f769-4484-b3f5-0892d9f6c118

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IsLeftCoactionIffIsCoactionComm
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Coalgebra
open GlobalTheory
variable {R : Type*} [CommSemiring R] {C : Type*} [AddCommMonoid C] [Module R C] [Coalgebra R C]
variable {M : Type*} [AddCommMonoid M] [Module R M] {M' : Type*} [AddCommMonoid M'] [Module R M']
variable (R C)
theorem _root_.solution : IsLeftCoaction (comul : C →ₗ[R] C ⊗[R] C) := by
  first
    | (intros; simp [IsLeftCoaction])
    | (intros; unfold IsLeftCoaction; simp)
    | (intros; simp [IsLeftCoaction]; done)
    | (intros; ext; simp [IsLeftCoaction])
    | (intros; simp only [IsLeftCoaction]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [IsLeftCoaction])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [IsLeftCoaction])
    | (intros; unfold IsLeftCoaction; split_ifs <;> simp_all)
    | (intros; unfold IsLeftCoaction; positivity)
    | (intros; unfold IsLeftCoaction; ring)
    | (intros; unfold IsLeftCoaction; exact?)
    | (intros; aesop (add norm simp [IsLeftCoaction]))
    | (intros; simp [IsLeftCoaction] <;> aesop)
    | (intros; exact IsLeftCoaction.symm ..)
    | (intros; exact IsLeftCoaction.comm ..)
  trace "HIT_91_1"

