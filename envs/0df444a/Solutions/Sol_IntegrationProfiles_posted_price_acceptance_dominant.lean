-- Prove2me | solution 1 for IntegrationProfiles.posted_price_acceptance_dominant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:11.614428+00:00
-- url     : https://prove2.me/submissions/87d29257-8f5a-4216-b526-425730183189


import Definitions.Def_IntegrationProfiles

set_option autoImplicit true
open IntegrationProfiles
namespace IntegrationProfiles
theorem _root_.solution (r : Nat) (e : Bool) (c b : Nat) :
    postedUtility r e c b ≤ postedUtility r e c (accept r c) := by
  unfold postedUtility accept postedWins
  cases e <;> by_cases hc : c ≤ r <;> by_cases hb : b ≤ r <;> simp [hc, hb] <;> omega
end IntegrationProfiles
