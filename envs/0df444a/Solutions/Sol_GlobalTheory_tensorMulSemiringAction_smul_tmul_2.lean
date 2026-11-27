-- Prove2me | solution 2 for GlobalTheory.tensorMulSemiringAction_smul_tmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:42:33.10536+00:00
-- url     : https://prove2.me/submissions/894bf6f6-119c-4f8e-81ff-ae152e7f03e1

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
variable (G : Type*) [Group G]
variable (R S A : Type*) [CommRing R] [CommRing S] [CommRing A] [Algebra R S] [Algebra R A]
  [MulSemiringAction G A] [SMulCommClass G R A]
namespace GlobalTheory
theorem _root_.solution (g : G) (s : S) (a : A) :
    letI := tensorMulSemiringAction G R S A
    g • (s ⊗ₜ[R] a) = s ⊗ₜ[R] (g • a) := rfl
end GlobalTheory
