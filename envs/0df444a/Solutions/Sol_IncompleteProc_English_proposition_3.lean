-- Prove2me | solution 1 for IncompleteProc.English.proposition_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T18:44:12.156183+00:00
-- url     : https://prove2.me/submissions/11b123fa-ba87-47ee-bc8c-2fcb39476aa5

import Mathlib
import Definitions.Def_IncompleteProc_English_Model
import Definitions.Def_IncompleteProc_English_Auction
import Theorems.Thm_IncompleteProc_English_win_payoff_sign
import Theorems.Thm_IncompleteProc_English_offer_optimal
import Theorems.Thm_IncompleteProc_English_proposition_1
import Theorems.Thm_IncompleteProc_English_english_surplus_eq_optimal

open MeasureTheory IncompleteProc.English

theorem solution {Ω : Type*} [MeasurableSpace Ω] (E : Env Ω) (hS : E.Standing)
    (hA : E.Assumption1) :
    (∀ c ∈ Set.Icc E.clo E.chi, ∀ x ∈ Set.Icc E.clo E.chi,
        (c ≤ x → 0 ≤ E.winPayoff c x) ∧ (x < c → E.winPayoff c x < 0)) ∧
    (∀ p ∈ Set.Ioc E.clo E.chi, ∀ ω,
        (∀ c ∈ Set.Icc E.clo p, E.offerValue ω p c ≤ E.offerValue ω p (min p (E.cStar2 ω))) ∧
        E.offer ω p = E.k (min p (E.cStar2 ω)) ω) ∧
    IsGreatest E.feasibleSurplus E.englishSurplus := by
  refine ⟨win_payoff_sign E hS hA, offer_optimal E hS hA, ?_⟩
  rw [english_surplus_eq_optimal E hS hA]
  exact (proposition_1 E hS hA).2.2.2
