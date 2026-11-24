-- Prove2me | solution 1 for GlobalTheory.ZetaFractionalIntegral.integrableOn_cpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:20:13.014288+00:00
-- url     : https://prove2.me/submissions/279e5834-6ab7-46d1-aa05-5a65249a57ba

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ZetaEqSubIntegralFract

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.ZetaFractionalIntegral
open MeasureTheory Set Filter Asymptotics
namespace GlobalTheory.ZetaFractionalIntegral
theorem _root_.solution {s : ℂ} (hs : 1 < s.re) :
    IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioi 1) := integrableOn_Ioi_cpow_of_lt (by simp only [Complex.neg_re]; linarith) one_pos
end GlobalTheory.ZetaFractionalIntegral
