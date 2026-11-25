-- Prove2me | solution 1 for GlobalTheory.Phase.pair_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:24.01322+00:00
-- url     : https://prove2.me/submissions/4bf687c6-9e32-4c57-90e0-f36462ff9bcc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IntMIffInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex
open GlobalTheory.SW
open GlobalTheory GlobalTheory.Phase
noncomputable section
variable {κ ι : Type} [Fintype κ] [Fintype ι]
variable {n g : ℕ}
namespace GlobalTheory.Phase
theorem _root_.solution {a b : Matrix κ ι ℚ} (ha : ∀ k i, ∃ z : ℤ, a k i = z) (hb : ∀ k i, ∃ z : ℤ, b k i = z) :
    ∃ z : ℤ, (∑ k, a k ⬝ᵥ b k : ℚ) = z := by
  choose A hA using ha
  choose B hB using hb
  refine ⟨∑ k, ∑ i, A k i * B k i, ?_⟩
  simp [dotProduct, hA, hB]
end GlobalTheory.Phase
