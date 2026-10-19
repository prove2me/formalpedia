-- Prove2me | solution 1 for IntMul.Kappa.campaign_bound_inv_two_pow_182
-- status  : ACCEPTED   (prove)
-- author  : @xuanji
-- created : 2026-10-18T15:03:47.644255+00:00
-- url     : https://prove2.me/submissions/06f3e39b-323c-43d8-984e-604577aa4b7b

-- OpenAI-preprint / κ-improvement development (integer-multiplication-kappa): target `IntMul.Kappa.campaign_bound_inv_two_pow_182`.
-- The bound is the published node `NLogN.KFTop.kappa_bound` (layer 5 of the κ pack).

import Theorems.Thm_NLogN_KFTop_kappa_bound

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

theorem solution : IntMul.KappaBound ((1 / 2 ^ 182) : ℝ) :=
  NLogN.KFTop.kappa_bound
