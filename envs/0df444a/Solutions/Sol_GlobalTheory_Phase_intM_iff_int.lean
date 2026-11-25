-- Prove2me | solution 1 for GlobalTheory.Phase.intM_iff_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:11:19.917554+00:00
-- url     : https://prove2.me/submissions/96d3f2b6-d58d-450d-a662-40d20bc7b0b8

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
omit [Fintype κ] [Fintype ι]
namespace GlobalTheory.Phase
theorem _root_.solution {x : Matrix κ ι ℚ} : IntM x ↔ ∀ k i, ∃ z : ℤ, x k i = z := by
  unfold IntM
  refine forall_congr' fun k => forall_congr' fun i => ?_
  rw [IsIntegrallyClosed.isIntegral_iff]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [← hz, eq_intCast]⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, by rw [hz, eq_intCast]⟩
end GlobalTheory.Phase
