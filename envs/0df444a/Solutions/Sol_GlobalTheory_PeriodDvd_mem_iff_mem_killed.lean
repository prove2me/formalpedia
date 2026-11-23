-- Prove2me | solution 1 for GlobalTheory.PeriodDvd.mem_iff_mem_killed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T07:53:16.743906+00:00
-- url     : https://prove2.me/submissions/b714af35-2616-4d9f-9ec0-a94d62d6cbfc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CardDvdSumOfInvariantOfCardStabilizerDvd
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_DvdOfPeriodOfDvdSumPowersetCard
import Theorems.Thm_GlobalTheory_PeriodDvd_mem_killed
import Theorems.Thm_GlobalTheory_PeriodDvd_card_killed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Pointwise
open GlobalTheory
open GlobalTheory.PeriodDvd
namespace GlobalTheory.PeriodDvd
theorem _root_.solution {d : ℕ} [NeZero d] (H : AddSubgroup (ZMod d)) (x : ZMod d) :
    x ∈ H ↔ x ∈ killed d (Nat.card H) := by
  classical
  have hdvd : Nat.card H ∣ d := by
    have := AddSubgroup.card_addSubgroup_dvd_card H
    rwa [Nat.card_zmod] at this
  obtain ⟨e, he⟩ := hdvd
  have hsub : Finset.univ.filter (· ∈ H) ⊆ killed d (Nat.card H) := by
    intro y hy
    have hy' : y ∈ H := (Finset.mem_filter.mp hy).2
    rw [mem_killed]
    have : Nat.card H • (⟨y, hy'⟩ : H) = 0 := card_nsmul_eq_zero'
    exact congrArg Subtype.val this
  have hc : (Finset.univ.filter (· ∈ H)).card = Nat.card H := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
  have := Finset.eq_of_subset_of_card_le hsub (by rw [hc, card_killed he.symm])
  rw [← this]
  simp
end GlobalTheory.PeriodDvd
