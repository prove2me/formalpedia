-- Prove2me | solution 1 for GlobalTheory.PositiveLowerBoundFinset.pos_lower_bound_on_finset
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T18:05:16.035943+00:00
-- url     : https://prove2.me/submissions/f66b0d7d-038d-452f-b8de-afe2bc331e24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PosLowerBoundOnFinset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.PositiveLowerBoundFinset
namespace GlobalTheory.PositiveLowerBoundFinset
theorem _root_.solution : ∀ {Y : Type} (T : Finset Y) (f : Y → ℝ),
    (∀ (P : Y), (0 : ℝ) < f P) → ∃ (r : ℝ), (0 : ℝ) < r ∧ ∀ P ∈ T, r ≤ f P := by
  intro Y T f hf
  rcases T.eq_empty_or_nonempty with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · obtain ⟨x, -, hmin⟩ := T.exists_min_image f h
    exact ⟨f x, hf x, hmin⟩
end GlobalTheory.PositiveLowerBoundFinset
