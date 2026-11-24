-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.finite_projective_invariants_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:14:25.252802+00:00
-- url     : https://prove2.me/submissions/e61e6ebf-126a-4d93-8a3e-acf70ad0a77e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_isFreeRingAction_iff_inertia_eq_bot
import Theorems.Thm_GlobalTheory_FreeQuotient_tame_descent
import Theorems.Thm_GlobalTheory_FreeQuotient_isBaseChange_invariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
open GlobalTheory.FreeQuotient
variable {G : Type*} [Group G] {A : Type*} [CommRing A] [MulSemiringAction G A]
variable [Finite G] (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
variable (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution (h : IsFreeRingAction G A) :
    (Module.Finite B (Representation.ofDistribMulAction B G M).invariants ∧
      Module.Projective B (Representation.ofDistribMulAction B G M).invariants) ↔
    (Module.Finite A M ∧ Module.Projective A M) := by
  have hb := isBaseChange_invariants B M h
  refine ⟨fun ⟨_, _⟩ ↦ ⟨.equiv hb.equiv, .of_equiv' hb.equiv⟩, fun ⟨_, _⟩ ↦ ?_⟩
  have hi := (isFreeRingAction_iff_inertia_eq_bot G A).mp h
  refine (tame_descent (A := A) B M (fun P hP ↦ ?_) fun P hP g hg m ↦ ?_).2
  · rw [hi P hP]
    simpa using (Ideal.ne_top_iff_one P).mp hP.ne_top
  · rw [hi P hP, Subgroup.mem_bot] at hg
    simp [hg]
end GlobalTheory.FreeQuotient
