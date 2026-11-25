-- Prove2me | solution 1 for GlobalTheory.isSaturatedIn_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:47:11.427117+00:00
-- url     : https://prove2.me/submissions/50c26347-235f-4e04-b5fb-150d817f9732

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_MemSaturatedOrderIsoSubspaceSpanSymmApply
import Theorems.Thm_GlobalTheory_submoduleOf_saturationIn
import Theorems.Thm_GlobalTheory_map_subtype_saturation_submoduleOf

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
theorem _root_.solution {M N : Submodule R V} :
    IsSaturatedIn M N ↔ N ≤ M ∧ IsSaturatedSubmodule (N.submoduleOf M) := by
  constructor
  · intro hs
    refine ⟨hs.le, ?_⟩
    unfold IsSaturatedSubmodule
    rw [← submoduleOf_saturationIn, hs.saturationIn_eq]
  · rintro ⟨hle, hs⟩
    unfold IsSaturatedIn
    rw [← map_subtype_saturation_submoduleOf, hs.saturation_eq, Submodule.submoduleOf,
      Submodule.map_comap_subtype, inf_of_le_right hle]
end GlobalTheory
