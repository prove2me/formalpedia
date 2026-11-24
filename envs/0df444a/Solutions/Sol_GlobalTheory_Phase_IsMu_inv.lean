-- Prove2me | solution 1 for GlobalTheory.Phase.IsMu.inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T19:26:02.615274+00:00
-- url     : https://prove2.me/submissions/6a3699db-2a5c-4b1f-9cfd-94e1c8fcf72f

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
namespace IsMu
theorem _root_.solution {a : ℂ} (ha : IsMu a) : IsMu a⁻¹ := by
  obtain ⟨m, hm, h⟩ := ha
  exact ⟨m, hm, by rw [inv_pow, h, inv_one]⟩
end IsMu
end GlobalTheory.Phase
