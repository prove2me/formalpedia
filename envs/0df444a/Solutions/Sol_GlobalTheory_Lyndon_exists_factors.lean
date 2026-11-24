-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_factors
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:29:38.865645+00:00
-- url     : https://prove2.me/submissions/442b0f04-36c5-4479-b6eb-1bff8060d1d0

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_isLyndon_singleton
import Theorems.Thm_GlobalTheory_Lyndon_exists_factors_cons

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
theorem _root_.solution (w : List A) : ∃ L, IsFactors L ∧ L.flatten = w := by
  induction w with
  | nil => exact ⟨[], ⟨by simp, by simp⟩, rfl⟩
  | cons a w ih =>
    obtain ⟨L, h1, h2⟩ := ih
    obtain ⟨L', h3, h4⟩ := exists_factors_cons L h1 [a] (isLyndon_singleton a)
    exact ⟨L', h3, by simp [h4, h2]⟩
end GlobalTheory.Lyndon
