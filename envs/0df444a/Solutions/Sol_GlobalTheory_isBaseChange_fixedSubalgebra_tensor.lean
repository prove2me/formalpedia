-- Prove2me | solution 1 for GlobalTheory.isBaseChange_fixedSubalgebra_tensor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:01:27.007456+00:00
-- url     : https://prove2.me/submissions/b0a48a49-5691-486a-befa-33901c7be9e8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Theorems.Thm_GlobalTheory_isBaseChange_fixedSubalgebraMap

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
theorem _root_.solution [Finite G] [Module.Flat R S] :
    letI := tensorMulSemiringAction G R S A
    haveI := tensorMulSemiringAction_smulCommClass G R S A
    IsBaseChange S (fixedSubalgebraMap G S
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) (tensorMulSemiringAction_includeRight G R S A)).toLinearMap := by
  letI := tensorMulSemiringAction G R S A
  haveI := tensorMulSemiringAction_smulCommClass G R S A
  have hb : IsBaseChange S
      (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).toLinearMap :=
    TensorProduct.isBaseChange R A S
  exact isBaseChange_fixedSubalgebraMap G
    (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A) hb
    (tensorMulSemiringAction_includeRight G R S A)
end GlobalTheory
