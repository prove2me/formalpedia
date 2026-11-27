-- Prove2me | solution 1 for GlobalTheory.saturation_eq_of_le_of_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:23.021088+00:00
-- url     : https://prove2.me/submissions/ac66bb78-e587-42f0-9876-42e473d0b770

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
theorem _root_.solution {N P : Submodule R M} (h₁ : N ≤ P) (h₂ : P ≤ saturation N) :
    saturation P = saturation N := le_antisymm ((saturation_mono h₂).trans (saturation_saturation N).le) (saturation_mono h₁)
end GlobalTheory
