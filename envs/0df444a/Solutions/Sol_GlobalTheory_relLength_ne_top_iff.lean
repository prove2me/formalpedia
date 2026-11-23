-- Prove2me | solution 1 for GlobalTheory.relLength_ne_top_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:01:39.124262+00:00
-- url     : https://prove2.me/submissions/f516bce0-4918-4a2c-a043-81f6c11dc47f

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_LengthCommensurableMapIffOfInjective

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
theorem _root_.solution {A B : Submodule R V} :
    relLength A B ≠ ⊤ ↔ IsFiniteLength R (A ⧸ B.submoduleOf A) :=
  Module.length_ne_top_iff
end GlobalTheory
