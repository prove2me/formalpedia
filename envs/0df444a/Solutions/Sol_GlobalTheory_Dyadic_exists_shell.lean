-- Prove2me | solution 1 for GlobalTheory.Dyadic.exists_shell
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:34:23.504392+00:00
-- url     : https://prove2.me/submissions/9b9e6aeb-08d6-4f60-a7e9-f5e0b8543569

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_LintegralBoundByDyadicSummation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped ENNReal
open GlobalTheory GlobalTheory.Dyadic
namespace GlobalTheory.Dyadic
theorem _root_.solution (s H : ℝ) (hH : 0 < H) :
    ∃ i : ℕ, s ≤ 2 ^ i * H ∧ (i = 0 ∨ 2 ^ i * H / 2 < s) := by
  have hex : ∃ i : ℕ, s ≤ 2 ^ i * H := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (s / H) (one_lt_two (α := ℝ))
    exact ⟨n, ((div_lt_iff₀ hH).1 hn).le⟩
  classical
  refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
  rcases h : Nat.find hex with _ | j
  · exact Or.inl rfl
  · right
    have := Nat.find_min hex (m := j) (by omega)
    push Not at this
    rw [pow_succ]; linarith
end GlobalTheory.Dyadic
