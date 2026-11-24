-- Prove2me | solution 1 for GlobalTheory.InjectiveAlgebraHomExistence.exists_algHom_of_injective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:47:53.586197+00:00
-- url     : https://prove2.me/submissions/8ade442b-0563-4f60-8b94-b36d99cf7afb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsRingHomCompAlgebraMapEq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1 u_2 u_3
open GlobalTheory GlobalTheory.InjectiveAlgebraHomExistence
namespace GlobalTheory.InjectiveAlgebraHomExistence
theorem _root_.solution {A : Type u_1} {B : Type u_2} {K : Type u_3}
    [CommRing A] [IsDomain A] [CommRing B] [IsDomain B] [Field K] [IsAlgClosed K]
    [Algebra A B] [Algebra A K] [Algebra.IsIntegral A B]
    (hB : Function.Injective (algebraMap A B)) (hK : Function.Injective (algebraMap A K)) :
    Nonempty (B →ₐ[A] K) := by
  haveI : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective _ _).2 hB
  haveI : FaithfulSMul A K := (faithfulSMul_iff_algebraMap_injective _ _).2 hK
  exact ⟨IsAlgClosed.lift⟩
end GlobalTheory.InjectiveAlgebraHomExistence
