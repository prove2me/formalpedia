-- Prove2me | solution 1 for GlobalTheory.isInvariant_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:40:09.616652+00:00
-- url     : https://prove2.me/submissions/9f712091-1fee-4350-848f-781c3d7cfaa6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isInvariant_of_isBaseChange

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
theorem _root_.solution [Finite G] [Module.Flat R S] [Algebra.IsInvariant R A G] :
    letI := tensorMulSemiringAction G R S A
    Algebra.IsInvariant S (S ⊗[R] A) G :=
  letI := tensorMulSemiringAction G R S A
  haveI := tensorMulSemiringAction_smulCommClass G R S A
  isInvariant_of_isBaseChange G (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A)
    (TensorProduct.isBaseChange R A S) (tensorMulSemiringAction_includeRight G R S A)
end GlobalTheory
