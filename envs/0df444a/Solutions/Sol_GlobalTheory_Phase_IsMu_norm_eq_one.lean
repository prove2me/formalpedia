-- Prove2me | solution 1 for GlobalTheory.Phase.IsMu.norm_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:15:38.898922+00:00
-- url     : https://prove2.me/submissions/52de6f57-9c0e-4ab7-a8c7-b9e37c518ba0

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
theorem _root_.solution {a : ℂ} (ha : IsMu a) : ‖a‖ = 1 := by
  obtain ⟨m, hm, h⟩ := ha
  have h1 : ‖a‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg a) hm.ne').1 h1
end IsMu
end GlobalTheory.Phase
