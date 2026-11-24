-- Prove2me | solution 1 for GlobalTheory.Lyndon.exists_cut
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T17:24:10.131132+00:00
-- url     : https://prove2.me/submissions/4375a807-604d-44b3-8be8-3f43e7db8bcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds

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
theorem _root_.solution (m : List A) (F : List (List A)) (hF : F.Pairwise (· ≥ ·)) :
    ∃ P R, F = P ++ R ∧ (∀ f ∈ P, m ≤ f) ∧ ∀ f ∈ R, f ≤ m := by
  induction F with
  | nil => exact ⟨[], [], rfl, by simp, by simp⟩
  | cons f F ih =>
    rcases le_total m f with h | h
    · obtain ⟨P, R, e, h1, h2⟩ := ih (List.pairwise_cons.1 hF).2
      refine ⟨f :: P, R, by simp [e], ?_, h2⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact h1 x hx
    · refine ⟨[], f :: F, rfl, by simp, ?_⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact h
      · exact le_trans ((List.pairwise_cons.1 hF).1 x hx) h
end GlobalTheory.Lyndon
