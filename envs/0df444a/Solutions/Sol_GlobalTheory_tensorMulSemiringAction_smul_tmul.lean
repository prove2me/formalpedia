-- Prove2me | solution 1 for GlobalTheory.tensorMulSemiringAction_smul_tmul
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:12:34.794634+00:00
-- url     : https://prove2.me/submissions/a43d2865-1953-4cb1-8e55-89ca3b2c5988

import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Mathlib


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Pointwise
open GlobalTheory
variable (G : Type*) [Group G]
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
theorem _root_.solution (g : G) (s : S) (a : A) :
    letI := tensorMulSemiringAction G R S A
    g • (s ⊗ₜ[R] a) = s ⊗ₜ[R] (g • a) := by
  first
    | (intros; simp [tensorMulSemiringAction])
    | (intros; unfold tensorMulSemiringAction; simp)
    | (intros; simp [tensorMulSemiringAction]; done)
    | (intros; ext; simp [tensorMulSemiringAction])
    | (intros; simp only [tensorMulSemiringAction]; rfl)
    | (intros; constructor <;> intro h <;> simp_all [tensorMulSemiringAction])
    | (intros; refine ⟨?_, ?_⟩ <;> simp [tensorMulSemiringAction])
    | (intros; unfold tensorMulSemiringAction; split_ifs <;> simp_all)
    | (intros; unfold tensorMulSemiringAction; positivity)
    | (intros; unfold tensorMulSemiringAction; ring)
    | (intros; unfold tensorMulSemiringAction; exact?)
    | (intros; aesop (add norm simp [tensorMulSemiringAction]))
    | (intros; simp [tensorMulSemiringAction] <;> aesop)
    | (intros; exact tensorMulSemiringAction.symm ..)
    | (intros; exact tensorMulSemiringAction.comm ..)
  trace "HIT_11_3"

