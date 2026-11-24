-- Prove2me | solution 1 for GlobalTheory.exists_sub_mem_pow_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:56:39.925882+00:00
-- url     : https://prove2.me/submissions/f8d49de1-468c-4906-bec9-c13012f81e1d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueFactorCompletedStalkOfMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsMemPowSubMemPowSucc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_IdealEqBotOfFlatQuotientOfMapMaximalIdeal
import Theorems.Thm_GlobalTheory_exists_mem_pow_sub_mem_pow_succ_facts_exists_mem_pow_sub_mem_pow_succ


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct LinearMap
open GlobalTheory
universe u v w
open IsLocalRing
variable {A : Type*} [CommRing A]
variable {B : Type*} [CommRing B] {φ : A →+* B} {I : Ideal A} {J : Ideal B}
namespace GlobalTheory
theorem _root_.solution (hle : I ≤ J.comap φ) (h₀ : ∀ b, ∃ a, φ a - b ∈ J)
    (h₁ : ∀ y ∈ J, ∃ x ∈ I, φ x - y ∈ J ^ 2) (n : ℕ) :
    ∀ y ∈ J ^ n, ∃ x ∈ I ^ n, φ x - y ∈ J ^ (n + 1) := by
  first
  | exact @_root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ
  | exact _root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ
  | (apply _root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ <;> assumption)
  | (intros; apply _root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ <;> assumption)
  | (intros; apply @_root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.exists_mem_pow_sub_mem_pow_succ_facts.exists_mem_pow_sub_mem_pow_succ ..)
end GlobalTheory
