-- Prove2me | solution 1 for GlobalTheory.QCoh.fibreMap_surjective_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:42:45.799154+00:00
-- url     : https://prove2.me/submissions/2952b3e3-77d6-4e61-9bb1-bee13eaf2ff3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_fibreMk_surjective
import Theorems.Thm_GlobalTheory_QCoh_map_fibreMk_eq_top_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite TensorProduct IsLocalRing
universe u
noncomputable section
open GlobalTheory GlobalTheory.QCoh
variable {X : Scheme.{u}} {F G H : X.Modules} {U V : X.Opens}
namespace GlobalTheory.QCoh
theorem _root_.solution (φ : F ⟶ G) [IsFiniteQC G] (x : X) :
    Function.Surjective (fibreMap φ x) ↔ Function.Surjective (stalkLinear φ x) := by
  refine ⟨fun h ↦ ?_, fun h ↦ LinearMap.lTensor_surjective _ h⟩
  rw [← LinearMap.range_eq_top, ← map_fibreMk_eq_top_iff, eq_top_iff]
  intro v _
  obtain ⟨w, rfl⟩ := h v
  obtain ⟨t, rfl⟩ := fibreMk_surjective F x w
  exact ⟨_, ⟨t, rfl⟩, rfl⟩
end GlobalTheory.QCoh
