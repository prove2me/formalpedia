-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_iff_smul_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T04:38:59.624505+00:00
-- url     : https://prove2.me/submissions/5ff0400f-05d1-4f02-8c07-b3d4fd2ecd3d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_mem_saturationIn_iff

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
variable {R : Type*} [CommRing R] {V V' : Type*} [AddCommGroup V] [Module R V]
  [AddCommGroup V'] [Module R V']
namespace GlobalTheory
theorem _root_.solution [IsDomain R] {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ ∀ a : R, a ≠ 0 → ∀ x ∈ M, a • x ∈ N → x ∈ N := by
  constructor
  · intro hs
    refine ⟨hs.le, fun a ha x hx hax => ?_⟩
    rw [← hs.saturationIn_eq]
    exact mem_saturationIn_iff.2 ⟨hx, a, ha, hax⟩
  · rintro ⟨hle, hs⟩
    show saturationIn M N = N
    refine le_antisymm (fun x hx => ?_) (le_saturationIn hle)
    obtain ⟨hxM, a, ha, hax⟩ := mem_saturationIn_iff.1 hx
    exact hs a ha x hxM hax
end GlobalTheory
