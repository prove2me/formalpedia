-- Prove2me | solution 1 for GlobalTheory.isSaturatedSubmodule_top
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:10:16.483032+00:00
-- url     : https://prove2.me/submissions/9108ca81-994a-4bc0-b93e-b30f757b3294

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors Pointwise
open GlobalTheory
variable {R : Type*} [CommRing R] {M M' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup M'] [Module R M']
theorem _root_.solution : IsSaturatedSubmodule (⊤ : Submodule R M) := by
  show GlobalTheory.saturation (⊤ : Submodule R M) = ⊤
  rw [eq_top_iff]
  intro x _
  rw [GlobalTheory.mem_saturation_iff']
  exact ⟨1, one_mem _, trivial⟩

