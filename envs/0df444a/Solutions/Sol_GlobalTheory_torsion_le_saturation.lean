-- Prove2me | solution 1 for GlobalTheory.torsion_le_saturation
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T03:10:09.0599+00:00
-- url     : https://prove2.me/submissions/f3562de6-1e99-4ba1-b4ae-e88b6813396c

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
theorem _root_.solution (N : Submodule R M) : Submodule.torsion R M ≤ saturation N := by
  intro x hx
  rw [GlobalTheory.mem_saturation_iff']
  obtain ⟨a, ha⟩ := (Submodule.mem_torsion_iff x).1 hx
  refine ⟨(a : R), a.2, ?_⟩
  have h0 : (a : R) • x = 0 := ha
  rw [h0]; exact zero_mem _

