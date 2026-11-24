-- Prove2me | solution 1 for IntegrationProfiles.fixed_reward_not_truthful
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T07:25:11.057809+00:00
-- url     : https://prove2.me/submissions/40f975c1-3af1-4641-aa54-835556ceb241


import Definitions.Def_IntegrationProfiles

set_option autoImplicit true
open IntegrationProfiles
namespace IntegrationProfiles
theorem _root_.solution :
    fixedRewardUtility 100 100 [50] [] 60 40 > fixedRewardUtility 100 100 [50] [] 60 60 := by
  decide
end IntegrationProfiles
