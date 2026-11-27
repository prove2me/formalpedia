-- Prove2me | solution 2 for GlobalTheory.saturation_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:41:28.444265+00:00
-- url     : https://prove2.me/submissions/ac105aa8-b79c-4383-8ef5-da2bbf96296b

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution {M N : Submodule R V} (h : N ≤ M) :
    saturation (saturationIn M N) = saturation N := by
  rw [saturationIn_def, saturation_inf, saturation_saturation, inf_of_le_right (saturation_mono h)]
end GlobalTheory
