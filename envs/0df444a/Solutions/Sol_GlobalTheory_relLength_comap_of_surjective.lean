-- Prove2me | solution 1 for GlobalTheory.relLength_comap_of_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:45:42.364027+00:00
-- url     : https://prove2.me/submissions/319b6150-37e1-462a-af87-d1f873db04c6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective
import Theorems.Thm_GlobalTheory_relLength_comap_of_le_range

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
theorem _root_.solution (f : V →ₛₗ[σ] V') (hf : Function.Surjective f)
    (A' B' : Submodule S V') : relLength (A'.comap f) (B'.comap f) = relLength A' B' :=
  relLength_comap_of_le_range f (by rw [LinearMap.range_eq_top.mpr hf]; exact le_top) B'
end GlobalTheory
