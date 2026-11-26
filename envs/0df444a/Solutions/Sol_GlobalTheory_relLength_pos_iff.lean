-- Prove2me | solution 1 for GlobalTheory.relLength_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:09:18.035265+00:00
-- url     : https://prove2.me/submissions/c473a778-efe0-457b-b196-6a9a52fb120e

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
theorem _root_.solution {A B : Submodule R V} : 0 < relLength A B ↔ ¬ A ≤ B := by
  rw [pos_iff_ne_zero, Ne, GlobalTheory.relLength_eq_zero_iff]

