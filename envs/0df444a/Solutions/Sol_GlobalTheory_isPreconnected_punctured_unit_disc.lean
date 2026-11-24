-- Prove2me | solution 1 for GlobalTheory.isPreconnected_punctured_unit_disc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:36:06.477169+00:00
-- url     : https://prove2.me/submissions/e8a1c32f-5798-4fc1-843c-ae65589deccd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_IsPreconnectedPolydiscFirstCoordsNeZero
import Theorems.Thm_GlobalTheory_punctured_unit_disc_eq_exp_image

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    IsPreconnected (Metric.ball (0:ℂ) 1 \ {0}) := by
  rw [punctured_unit_disc_eq_exp_image]
  exact (convex_halfSpace_re_lt 0).isPreconnected.image _ Complex.continuous_exp.continuousOn
end GlobalTheory
