-- Prove2me | solution 1 for GlobalTheory.T.linearIndepOn_frob_pow_of_isDomain_tensor_insep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:25:46.941317+00:00
-- url     : https://prove2.me/submissions/f717e76b-cbaa-4b57-8dec-d7afd2c41171

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparabl
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinearIndepOnPowOfIsDomainTensorPurelyInseparablStatement
import Theorems.Thm_GlobalTheory_linearIndepOn_pow_of_isDomain_tensor_purelyInseparable


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (k B : Type) [Field k] [CommRing B] [IsDomain B] [Algebra k B] (p : ℕ), p.Prime → CharP k p → (∀ (K : Type) [Field K] [Algebra k K], FiniteDimensional k K → IsPurelyInseparable k K → IsDomain (K ⊗[k] B)) → ∀ s : Finset (FractionRing B), LinearIndepOn k _root_.id (s : Set (FractionRing B)) → LinearIndepOn k (· ^ p) (s : Set (FractionRing B)) := by
  first | exact @GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | exact GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable | (intros; apply GlobalTheory.linearIndepOn_pow_of_isDomain_tensor_purelyInseparable <;> assumption)
end _root_.GlobalTheory.T
