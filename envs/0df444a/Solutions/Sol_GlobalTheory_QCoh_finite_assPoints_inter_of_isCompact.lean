-- Prove2me | solution 1 for GlobalTheory.QCoh.finite_assPoints_inter_of_isCompact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:22:28.284333+00:00
-- url     : https://prove2.me/submissions/0ae16b26-98cf-4fe6-a4ee-1d8b5694a277

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_finite_assPoints_inter_affine

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
variable [IsLocallyNoetherian X]
variable (F)
namespace GlobalTheory.QCoh
theorem _root_.solution [IsFiniteQC F] {K : Set X} (hK : IsCompact K) :
    (assPoints F ∩ K).Finite := by
  choose W hW hxW using exists_affine_mem (X := X)
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x ↦ (W x : Set X)) (fun x ↦ (W x).2)
    fun x _ ↦ Set.mem_iUnion.2 ⟨x, hxW x⟩
  refine (t.finite_toSet.biUnion fun x _ ↦ finite_assPoints_inter_affine F (hW x)).subset
    fun y hy ↦ ?_
  obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.1 (ht hy.2)
  exact Set.mem_iUnion₂.2 ⟨x, hx, hy.1, hyx⟩
end GlobalTheory.QCoh
