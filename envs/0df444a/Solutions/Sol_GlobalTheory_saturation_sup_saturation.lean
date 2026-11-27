-- Prove2me | solution 1 for GlobalTheory.saturation_sup_saturation
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:24.624913+00:00
-- url     : https://prove2.me/submissions/197a75e6-e350-4944-8bcf-90298ff4853b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
namespace GlobalTheory
theorem _root_.solution (N P : Submodule R M) :
    saturation (saturation N ⊔ saturation P) = saturation (N ⊔ P) := by
  refine le_antisymm ?_ (saturation_mono (sup_le_sup (le_saturation N) (le_saturation P)))
  calc saturation (saturation N ⊔ saturation P) ≤ saturation (saturation (N ⊔ P)) :=
        saturation_mono (sup_le (saturation_mono le_sup_left) (saturation_mono le_sup_right))
    _ = saturation (N ⊔ P) := saturation_saturation _
end GlobalTheory
