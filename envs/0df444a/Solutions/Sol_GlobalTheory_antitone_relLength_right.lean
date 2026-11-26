-- Prove2me | solution 1 for GlobalTheory.antitone_relLength_right
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:09:29.643598+00:00
-- url     : https://prove2.me/submissions/244b54ee-3c45-4c13-8d92-ce832dc4f05b

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
theorem _root_.solution (A : Submodule R V) : Antitone (relLength A) := by
  exact fun B B' h => GlobalTheory.relLength_anti_right A h

