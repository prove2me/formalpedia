-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.finite_invariants_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:44:02.980056+00:00
-- url     : https://prove2.me/submissions/aea3d81a-0cc2-4967-b135-13046195711a

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime
import Theorems.Thm_GlobalTheory_FreeQuotient_faithfullyFlat
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
    Module.Finite B (Representation.ofDistribMulAction B G M).invariants ↔ Module.Finite A M := by
  have hb := isBaseChange_invariants B M h
  haveI := faithfullyFlat B h
  refine ⟨fun _ ↦ .equiv hb.equiv, fun _ ↦ ?_⟩
  haveI := Module.Finite.equiv hb.equiv.symm
  exact Module.Finite.of_finite_tensorProduct_of_faithfullyFlat A
end GlobalTheory.FreeQuotient
