-- Prove2me | solution 1 for GlobalTheory.piTensorDistribMulAction_smul_tprod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:29:10.921401+00:00
-- url     : https://prove2.me/submissions/6391f3dc-0b0f-4017-8669-4096f8fff062

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
theorem _root_.solution (g : G) (x : ∀ i, M i) :
    letI := piTensorDistribMulAction G A M
    g • PiTensorProduct.tprod A x = PiTensorProduct.tprod A fun i ↦ g • x i :=
  piTensorMapₛₗ_tprod _ _ x
end GlobalTheory
