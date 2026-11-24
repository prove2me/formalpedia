-- Prove2me | solution 1 for IntegrationProfiles.fixed_reward_lowest_bid_weakly_better
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:13.796286+00:00
-- url     : https://prove2.me/submissions/805ea82e-db6a-480b-a3dc-97a36907e1f8


import Definitions.Def_IntegrationProfiles

set_option autoImplicit true
open IntegrationProfiles
namespace IntegrationProfiles
theorem _root_.solution (reward r : Nat) (before after : List Nat) (c : Nat)
    (hc : c ≤ reward) :
    fixedRewardUtility reward r before after c c ≤ fixedRewardUtility reward r before after c 0 := by
  unfold fixedRewardUtility
  by_cases hw : ranks r before after c
  · have h0 : ranks r before after 0 := by
      obtain ⟨hr, hb, ha⟩ := hw
      exact ⟨Nat.zero_le _, fun x hx => Nat.lt_of_le_of_lt (Nat.zero_le _) (hb x hx),
             fun x _ => Nat.zero_le x⟩
    simp only [hw, h0, ite_true]
    exact Int.le_refl _
  · simp only [hw, ite_false]
    by_cases h0 : ranks r before after 0
    · simp only [h0, ite_true]; omega
    · simp only [h0, ite_false]; exact Int.le_refl _
end IntegrationProfiles
