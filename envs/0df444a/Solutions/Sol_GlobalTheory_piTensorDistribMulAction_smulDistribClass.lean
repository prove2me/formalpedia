-- Prove2me | solution 1 for GlobalTheory.piTensorDistribMulAction_smulDistribClass
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:10.225821+00:00
-- url     : https://prove2.me/submissions/a1c759da-52a4-48f0-8aa9-1f24d565cd2f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton

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
variable {G : Type*} [Group G] (A : Type*) [CommRing A] [MulSemiringAction G A]
variable (G) {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)] [∀ i, Module A (M i)]
  [∀ i, DistribMulAction G (M i)] [∀ i, SMulDistribClass G A (M i)]
namespace GlobalTheory
theorem _root_.solution :
    letI := piTensorDistribMulAction G A M
    SMulDistribClass G A (⨂[A] i, M i) :=
  letI := piTensorDistribMulAction G A M
  ⟨fun g a y ↦ map_smulₛₗ (piTensorMapₛₗ _ (fun i ↦ smulSemilinearMap A (M i) g)) a y⟩
end GlobalTheory
