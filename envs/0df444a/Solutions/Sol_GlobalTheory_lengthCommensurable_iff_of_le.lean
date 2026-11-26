-- Prove2me | solution 1 for GlobalTheory.lengthCommensurable_iff_of_le
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:10:02.163736+00:00
-- url     : https://prove2.me/submissions/4d2ce88d-101f-4e59-a2dc-f30a07ab0ab5

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
theorem _root_.solution (h : A ≤ B) :
    LengthCommensurable A B ↔ relLength B A ≠ ⊤ := by
  unfold GlobalTheory.LengthCommensurable
  rw [GlobalTheory.relLength_eq_zero_of_le h]
  simp

