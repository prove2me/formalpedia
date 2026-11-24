-- Prove2me | solution 1 for GlobalTheory.FreeQuotient.bijective_liftBaseChange_of_isBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:29.737101+00:00
-- url     : https://prove2.me/submissions/69eb5441-c612-4fb8-a3ab-250e64fe3dc9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsFreeRingActionIffInertiaEqBotOfIsPrime

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
variable {G : Type*} [Group G] [Finite G] {A : Type*} [CommRing A] [MulSemiringAction G A]
  (B : Type*) [CommRing B] [Algebra B A] [SMulCommClass G B A]
  [FaithfulSMul B A] [Algebra.IsInvariant B A G]
  (M : Type*) [AddCommGroup M] [Module A M] [DistribMulAction G M] [SMulDistribClass G A M]
  [Module B M] [IsScalarTower B A M] [SMulCommClass G B M]
omit [Finite G] [MulSemiringAction G A] [SMulCommClass G B A] [FaithfulSMul B A]
  [Algebra.IsInvariant B A G] [SMulDistribClass G A M]
namespace GlobalTheory.FreeQuotient
theorem _root_.solution
    (h : IsBaseChange A (Representation.ofDistribMulAction B G M).invariants.subtype) :
    Function.Bijective
      ((Representation.ofDistribMulAction B G M).invariants.subtype.liftBaseChange A) := by
  have : (Representation.ofDistribMulAction B G M).invariants.subtype.liftBaseChange A =
      h.equiv.toLinearMap := by
    ext x
    simp
  rw [this]
  exact h.equiv.bijective
end GlobalTheory.FreeQuotient
