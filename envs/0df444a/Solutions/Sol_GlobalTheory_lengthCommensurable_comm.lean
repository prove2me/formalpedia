-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_comm
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:09:54.795959+00:00
-- url     : https://prove2.me/submissions/4583ccd0-8803-4382-bccf-d50317096beb

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
variable {R V : Type*} [Ring R] [AddCommGroup V] [Module R V] {A B : Submodule R V}
theorem _root_.solution : LengthCommensurable A B ↔ LengthCommensurable B A := by
  unfold GlobalTheory.LengthCommensurable
  exact and_comm

