-- Prove2me | solution 1 for GlobalTheory.pow_mem_range_includeRight_of_isPurelyInseparable
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:29:50.642423+00:00
-- url     : https://prove2.me/submissions/0ed287ba-aadb-41fe-8959-d2dd7bf346ad

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsPowPowMemRangeIncludeRight
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IdempotentTensorEqZeroOrOneOfIsPurelyInseparable
import Theorems.Thm_GlobalTheory_PowerInRangeTensorRight_exists_pow_pow_mem_range_includeRight


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open scoped TensorProduct
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (k K B : Type) [Field k] [Field K]
    [Algebra k K] [IsPurelyInseparable k K] [CommRing B] [Nontrivial B] [Algebra k B]
    (q : ℕ) [ExpChar k q] (z : K ⊗[k] B) :
    ∃ n : ℕ, z ^ q ^ n ∈
      (Algebra.TensorProduct.includeRight : B →ₐ[k] K ⊗[k] B).range := by
  first
  | exact @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight
  | (apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerInRangeTensorRight.exists_pow_pow_mem_range_includeRight ..)
end GlobalTheory
