-- Prove2me | solution 1 for GlobalTheory.DI.Dtot_cup
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T14:49:18.408269+00:00
-- url     : https://prove2.me/submissions/7b427578-f01f-4dd6-8d0b-94dbb2f5a6cd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFlatLift
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CechDeltaCupProduct
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_NadelVanishingPairs_NadelVanishingLemmas_TotalDifferentialCupProduct
import Theorems.Thm_GlobalTheory_DI_delta_cup_eq


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory GlobalTheory.DI
open GlobalTheory GlobalTheory.DI
namespace GlobalTheory.DI
theorem _root_.solution : ∀ {ι : Type} [LinearOrder ι] {E : Type} [AddCommGroup E] (d : E →+ E)
    (Φ : E →+ (Finset ι → E)) (c : Finset ι → E), (∀ x, Φ x ∅ = 0) → c ∅ = 0 →
    (∀ s, Dtot d (Φ (c s)) = 0) → Dtot d (cup Φ c) = cup Φ (delta c) := by
  intro ι _ E _ d Φ c hΦ hc hD
  funext u
  have key := delta_cup_eq Φ c hΦ hc u
  suffices hS : (∑ j ∈ u, ((-1 : ℤ) ^ ({x ∈ u | x < j}).card) • delta (Φ (c ({x ∈ u | x ≤ j}))) ({x ∈ u | j ≤ x}))
      + ((-1 : ℤ) ^ u.card) • d (cup Φ c u) = 0 by
    simp only [Dtot]
    rw [key, add_assoc, hS, add_zero]
  simp only [cup, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun j hj => ?_
  have h := congrFun (hD ({x ∈ u | x ≤ j})) ({x ∈ u | j ≤ x})
  simp only [Dtot, Pi.zero_apply] at h
  rw [eq_neg_of_add_eq_zero_left h]
  have hcard : ({x ∈ u | x < j}).card + ({x ∈ u | j ≤ x}).card = u.card := by
    have := Finset.card_filter_add_card_filter_not (s := u) (fun x => x < j)
    simpa only [not_lt] using this
  rw [smul_neg, smul_smul, ← pow_add, hcard, neg_add_cancel]
end GlobalTheory.DI
