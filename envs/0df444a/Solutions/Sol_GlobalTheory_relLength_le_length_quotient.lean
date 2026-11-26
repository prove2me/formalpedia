-- Prove2me | solution 1 for GlobalTheory.relLength_le_length_quotient
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:09:46.969131+00:00
-- url     : https://prove2.me/submissions/b4aade67-bc42-430c-b6b9-7c65f3b08480

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
theorem _root_.solution (A B : Submodule R V) :
    relLength A B ≤ Module.length R (V ⧸ B) := by
  rw [← GlobalTheory.relLength_top_left]
  exact GlobalTheory.relLength_mono_left le_top B

