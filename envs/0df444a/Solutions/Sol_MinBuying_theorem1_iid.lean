-- Prove2me | solution 1 for MinBuying.theorem1_iid
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:08:01.406182+00:00
-- url     : https://prove2.me/submissions/f3ca124c-0a36-4a41-a126-272d18b6176d

import Theorems.Thm_MinBuying_iid_policy_domination

open MeasureTheory MinBuying

theorem solution (n : ℕ) (hn : 0 < n) (F : Measure ℝ)
    (hF : ValidMarginal F) (hpos : ∀ᵐ v ∂F, 0 < v)
    (hcont : F ≪ volume) (hopt : WellPosed (iidLaw n F)) :
    DPRevenue (iidLaw n F) = UPRevenue (iidLaw n F) := by
  rcases hopt with ⟨hDb, hUb, ⟨p, hp, hpopt⟩, ⟨q, hq, hqopt⟩, _⟩
  apply le_antisymm
  · obtain ⟨i, hi⟩ := iid_policy_domination n hn F hF p hp
    rw [← hpopt]
    exact hi.trans (le_csSup hUb ⟨p i, hp i, rfl⟩)
  · rw [← hqopt]
    exact le_csSup hDb ⟨fun _ => q, fun _ => hq, rfl⟩
