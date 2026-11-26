-- Prove2me | solution 1 for GlobalTheory.isCoaction_comul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:25:51.456801+00:00
-- url     : https://prove2.me/submissions/8c1ae5a2-bf93-4f4a-a62a-fdbb7af8954d

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
theorem _root_.solution : IsCoaction (comul : C →ₗ[R] C ⊗[R] C) := by
  first
    | (intros; simp [IsCoaction])
    | (intros; unfold IsCoaction; simp)
    | (intros; simp [IsCoaction]; done)
    | (intros; ext; simp [IsCoaction])
    | (intros; simp only [IsCoaction]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [IsCoaction])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [IsCoaction])
    | (intros; unfold IsCoaction; split_ifs <;> simp_all)
    | (intros; unfold IsCoaction; positivity)
    | (intros; unfold IsCoaction; ring)
    | (intros; unfold IsCoaction; exact?)
    | (intros; aesop (add norm simp [IsCoaction]))
    | (intros; simp [IsCoaction] <;> aesop)
    | (intros; exact IsCoaction.symm ..)
    | (intros; exact IsCoaction.comm ..)
  trace "HIT_91_0"

