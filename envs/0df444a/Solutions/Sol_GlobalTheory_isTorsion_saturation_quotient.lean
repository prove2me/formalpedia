-- Prove2me | solution 1 for GlobalTheory.isTorsion_saturation_quotient
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:11:26.984166+00:00
-- url     : https://prove2.me/submissions/31de59b4-ea84-4a43-87a6-9bc8518e0788

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
namespace GlobalTheory
theorem _root_.solution (N : Submodule R M) :
    Module.IsTorsion R (saturation N ⧸ N.submoduleOf (saturation N)) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ y
  obtain ⟨a, ha, hax⟩ := mem_saturation_iff'.1 x.2
  refine ⟨⟨a, ha⟩, ?_⟩
  show a • (N.submoduleOf (saturation N)).mkQ x = 0
  rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact hax
end GlobalTheory
