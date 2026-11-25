-- Prove2me | solution 1 for GlobalTheory.BadShare.card_perm_no_long_cycle
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:11:59.774339+00:00
-- url     : https://prove2.me/submissions/cf45c519-b2e4-4c31-8f21-5c3100e48239

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SamePartIffOfNeZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_MassDegTypeLeCycleTypeStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CardCycleTypeConsMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_CentralBinomLePowCardPrimesBetween
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_SquarefreeLabelTorusMassNoLargePrimeFactorLe
import Theorems.Thm_GlobalTheory_BadShare_add_le_sum_of_mem_of_ne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial Classical GlobalTheory.BadShare
open GlobalTheory GlobalTheory.BadShare
namespace GlobalTheory.BadShare
theorem _root_.solution (N : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, N < 2 * p) :
    (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts).card +
      ∑ p ∈ S, (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts).card = N.factorial := by
  have hsum : ∀ σ : Equiv.Perm (Fin N), σ.partition.parts.sum = N := fun σ => by
    simpa using σ.partition.parts_sum
  have hdisj : (S : Set ℕ).PairwiseDisjoint
      fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts := by
    intro p hp q hq hpq
    rw [Function.onFun, Finset.disjoint_filter]
    intro σ _ hpσ hqσ
    have h1 := add_le_sum_of_mem_of_ne hpσ hqσ hpq
    rw [hsum σ] at h1
    have h2 := hS p hp
    have h3 := hS q hq
    omega
  rw [← Finset.card_biUnion hdisj]
  have hc : (Finset.univ.filter fun σ : Equiv.Perm (Fin N) => ∀ p ∈ S, p ∉ σ.partition.parts) =
      (S.biUnion fun p => Finset.univ.filter fun σ : Equiv.Perm (Fin N) => p ∈ σ.partition.parts)ᶜ := by
    ext σ
    simp
  rw [hc, Finset.card_compl_add_card, Fintype.card_perm, Fintype.card_fin]
end GlobalTheory.BadShare
