-- Prove2me | solution 1 for GlobalTheory.HomExt.field_point_comp_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:50:56.400169+00:00
-- url     : https://prove2.me/submissions/57f607a2-a947-45ee-84b8-03f257fef5fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_FlatImageOfOverFractionFieldOfValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_LocallyQuasiFiniteOfFiniteGeometricPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoOfDensePartOfIsIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.HomExt
namespace GlobalTheory.HomExt
theorem _root_.solution {Z Y : Scheme.{0}} (g g' : Z ⟶ Y) {k : Type} [Field k]
    (c : Spec (.of k) ⟶ Z) (z : Z) (hz : z ∈ Set.range c) :
    c ≫ g = c ≫ g' ↔ Z.fromSpecResidueField z ≫ g = Z.fromSpecResidueField z ≫ g' := by
  obtain ⟨⟨w, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective c
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hz ⊢
  obtain rfl : z = w := by
    obtain ⟨t, rfl⟩ := hz
    exact (Scheme.Hom.comp_apply _ _ t).trans (Scheme.fromSpecResidueField_apply w _)
  have : Flat (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    letI := φ.hom.toAlgebra
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  have : Surjective (Spec.map φ) := ⟨fun t ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  have : Epi (Spec.map φ) := Flat.epi_of_flat_of_surjective _
  rw [Category.assoc, Category.assoc, cancel_epi]
end GlobalTheory.HomExt
