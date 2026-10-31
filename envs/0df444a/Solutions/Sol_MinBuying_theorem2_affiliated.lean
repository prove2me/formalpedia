-- Prove2me | solution 1 for MinBuying.theorem2_affiliated
-- status  : ACCEPTED   (prove)
-- author  : @mikeh
-- created : 2026-10-30T17:08:06.317174+00:00
-- url     : https://prove2.me/submissions/f0af5364-07a3-4dc6-b131-b63cde7e6bb8

import Theorems.Thm_MinBuying_affiliated_policy_domination

open MinBuying

theorem solution (n : ℕ) (hn : 0 < n) (μ : JointLaw n)
    (hμ : ValidLaw μ) (hex : Exchangeable μ) (haff : Affiliated μ)
    (hopt : WellPosed μ) :
    DPRevenue μ = UPRevenue μ := by
  rcases hopt with ⟨hDb, hUb, ⟨p, hp, hpopt⟩, ⟨q, hq, hqopt⟩, _⟩
  apply le_antisymm
  · obtain ⟨i, hi⟩ := affiliated_policy_domination n hn μ hμ hex haff p hp
    rw [← hpopt]
    exact hi.trans (le_csSup hUb ⟨p i, hp i, rfl⟩)
  · rw [← hqopt]
    exact le_csSup hDb ⟨fun _ => q, fun _ => hq, rfl⟩
