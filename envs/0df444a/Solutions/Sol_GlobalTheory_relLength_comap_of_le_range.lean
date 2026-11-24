-- Prove2me | solution 1 for GlobalTheory.relLength_comap_of_le_range
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:48.554129+00:00
-- url     : https://prove2.me/submissions/373a1e70-f13c-4d33-a671-c449397480bf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_comap_comap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
variable {R S V V' : Type*} [Ring R] [Ring S] [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module S V'] {σ : R →+* S} [RingHomSurjective σ]
namespace GlobalTheory
theorem _root_.solution (f : V →ₛₗ[σ] V') {A' : Submodule S V'}
    (hA : A' ≤ LinearMap.range f) (B' : Submodule S V') :
    relLength (A'.comap f) (B'.comap f) = relLength A' B' := by
  rw [relLength_comap_comap, inf_eq_right.mpr hA]
end GlobalTheory
