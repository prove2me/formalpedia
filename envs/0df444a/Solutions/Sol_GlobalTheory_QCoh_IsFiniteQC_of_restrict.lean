-- Prove2me | solution 1 for GlobalTheory.QCoh.IsFiniteQC.of_restrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:08:22.727451+00:00
-- url     : https://prove2.me/submissions/093cdfca-cf2b-4195-8ce6-8017abecdbf3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_IsLocalizedModuleGermLinearPointOfPrime
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_TopologicalKrullDimLeOfIrreducibleCloseds
import Theorems.Thm_GlobalTheory_QCoh_isQuasicoherent_of_restrict


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
attribute [instance 100] IsFiniteQC.isQuasicoherent
variable {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
namespace GlobalTheory.QCoh
namespace IsFiniteQC
theorem _root_.solution {ι : Type*} {Y : ι → Scheme.{u}} (g : ∀ i, Y i ⟶ X)
    [∀ i, IsOpenImmersion (g i)] (hcov : ∀ x : X, ∃ i, x ∈ (g i).opensRange)
    (h : ∀ i, IsFiniteQC (F.restrict (g i))) : IsFiniteQC F := by
  have := isQuasicoherent_of_restrict F g hcov fun i ↦ (h i).isQuasicoherent
  refine .of_forall_exists_affine fun x ↦ ?_
  obtain ⟨i, y, rfl⟩ := hcov x
  obtain ⟨W, hW, hy⟩ := exists_affine_mem y
  exact ⟨g i ''ᵁ W, hW.image_of_isOpenImmersion _, ⟨y, hy, rfl⟩,
    (finite_sections_restrict_iff F (g i) W).1 ((h i).finite_affine W hW)⟩
end IsFiniteQC
end GlobalTheory.QCoh
