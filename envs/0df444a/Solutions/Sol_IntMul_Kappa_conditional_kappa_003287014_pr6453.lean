-- Prove2me | solution 1 for IntMul.Kappa.conditional_kappa_003287014_pr6453
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @gustasmickus
-- created : 2026-11-08T00:24:23.898205+00:00
-- url     : https://prove2.me/submissions/91839c76-ad3c-4a91-9b7c-3856ee6c2079
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_IntMul_Kappa_pr6453_machine
import Theorems.Thm_IntMul_Kappa_kappaBound_of_polylog_slack
import Definitions.Def_IntMul_MultitapeModel

set_option autoImplicit false

theorem solution : IntMul.KappaBound (0.003287014 : ℝ) := by
  obtain ⟨M, g, C, A, n₀, hg, _hC, hcorr, hT⟩ := IntMul.Kappa.pr6453_machine
  exact IntMul.Kappa.kappaBound_of_polylog_slack 0.003287014 g C A hg M hcorr n₀ hT
