-- Prove2me | solution 1 for GlobalTheory.relLength_submoduleOf
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:45:30.426144+00:00
-- url     : https://prove2.me/submissions/3ac14e2f-a0b0-4c32-8a24-974d135c7ac2

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
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V]
namespace GlobalTheory
theorem _root_.solution {A W : Submodule R V} (h : A ≤ W) (B : Submodule R V) :
    relLength (A.submoduleOf W) (B.submoduleOf W) = relLength A B :=
  relLength_comap_of_le_range W.subtype (by rwa [Submodule.range_subtype]) B
end GlobalTheory
