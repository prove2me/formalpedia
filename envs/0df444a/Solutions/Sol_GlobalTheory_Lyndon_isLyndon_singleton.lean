-- Prove2me | solution 1 for GlobalTheory.Lyndon.isLyndon_singleton
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T18:53:24.028261+00:00
-- url     : https://prove2.me/submissions/c98405cb-5a53-465a-b2cf-6f3e4a2376f7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_isLyndon_of_pairwise_lt

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
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
namespace GlobalTheory.Lyndon
theorem _root_.solution (a : A) : IsLyndon [a] :=
  isLyndon_of_pairwise_lt (by simp) (by simp)
end GlobalTheory.Lyndon
