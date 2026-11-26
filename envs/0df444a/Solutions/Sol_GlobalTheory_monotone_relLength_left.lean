-- Prove2me | solution 1 for GlobalTheory.monotone_relLength_left
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:09:39.27982+00:00
-- url     : https://prove2.me/submissions/88f2242f-5597-48ea-a534-046ec430aec0

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
theorem _root_.solution (B : Submodule R V) : Monotone fun A => relLength A B := by
  exact fun A A' h => GlobalTheory.relLength_mono_left h B

