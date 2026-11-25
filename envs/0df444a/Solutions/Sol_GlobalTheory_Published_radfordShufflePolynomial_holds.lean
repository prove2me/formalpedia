-- Prove2me | solution 1 for GlobalTheory.Published.radfordShufflePolynomial_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:00:27.18211+00:00
-- url     : https://prove2.me/submissions/e8d6248e-1719-4d3f-8873-530e2d798b48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_aeval_injective
import Theorems.Thm_GlobalTheory_Lyndon_aeval_surjective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Published
namespace GlobalTheory.Published
theorem _root_.solution : RadfordShufflePolynomial :=
  fun K _ _ _ _ => ⟨Lyndon.aeval_injective K, Lyndon.aeval_surjective K⟩
end GlobalTheory.Published
