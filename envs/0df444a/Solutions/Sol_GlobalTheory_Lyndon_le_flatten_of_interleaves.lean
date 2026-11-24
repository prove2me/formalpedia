-- Prove2me | solution 1 for GlobalTheory.Lyndon.le_flatten_of_interleaves
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T19:46:32.592608+00:00
-- url     : https://prove2.me/submissions/aedcd3b8-60ae-424e-abe0-d08ac3603ea1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
import Theorems.Thm_GlobalTheory_Lyndon_append_lt_append_left
import Theorems.Thm_GlobalTheory_Lyndon_nil_le
import Theorems.Thm_GlobalTheory_Lyndon_exists_factors
import Theorems.Thm_GlobalTheory_Lyndon_interleaves_flatten
import Theorems.Thm_GlobalTheory_Lyndon_exists_factors_step

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
theorem _root_.solution (w : List A) : ∀ L : List (List A), IsFactors L →
    Interleaves w ↑L → w ≤ L.flatten := by
  induction w with
  | nil => exact fun L _ _ => nil_le _
  | cons a w ih =>
    rintro L hL ⟨u, T, e, h⟩
    obtain ⟨F, hF, hu⟩ := exists_factors u
    obtain ⟨L', h1, h2, h3⟩ := exists_factors_step hL hF hu e
    have h4 := interleaves_flatten w F T (hu ▸ h)
    rw [← h2] at h4
    refine le_trans ?_ h3
    rcases (ih L' h1 h4).lt_or_eq with h | h
    · exact (append_lt_append_left [a] h).le
    · rw [h]
end GlobalTheory.Lyndon
