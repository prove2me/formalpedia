-- Prove2me | solution 1 for GlobalTheory.span_localization_saturationIn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:39:46.745824+00:00
-- url     : https://prove2.me/submissions/1d5dce3d-c396-4a41-b8bb-e852143f8155

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_span_localization_saturation

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
variable {R : Type*} [CommRing R] (S : Type*) [CommRing S] [Algebra R S] (p : Submonoid R)
  [IsLocalization p S] {V : Type*} [AddCommGroup V] [Module R V] [Module S V]
  [IsScalarTower R S V]
include p
namespace GlobalTheory
theorem _root_.solution (hp : p ≤ R⁰) (M N : Submodule R V) :
    Submodule.span S (saturationIn M N : Set V) =
      saturationIn (Submodule.span S (M : Set V)) (Submodule.span S (N : Set V)) := by
  rw [saturationIn_def, saturationIn_def, span_localization_inf S p,
    span_localization_saturation S p hp]
end GlobalTheory
