-- Prove2me | solution 1 for GlobalTheory.saturation_smul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:44:21.518727+00:00
-- url     : https://prove2.me/submissions/b203b0ac-3394-441d-a290-6daf3136db6d

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
theorem _root_.solution [IsDomain R] (N : Submodule R M) {a : R} (ha : a ≠ 0) :
    saturation (a • N) = saturation N := by
  apply le_antisymm
  · apply saturation_mono
    intro x hx
    obtain ⟨y, hy, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hx
    exact N.smul_mem a hy
  · refine (isSaturatedSubmodule_saturation (a • N)).saturation_le_iff.2 fun x hx => ?_
    exact mem_saturation_of_smul_mem ha (Submodule.smul_mem_pointwise_smul x a N hx)
end GlobalTheory
