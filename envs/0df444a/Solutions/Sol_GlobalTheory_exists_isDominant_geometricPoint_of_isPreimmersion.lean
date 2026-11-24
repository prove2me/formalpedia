-- Prove2me | solution 1 for GlobalTheory.exists_isDominant_geometricPoint_of_isPreimmersion
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:42:34.150114+00:00
-- url     : https://prove2.me/submissions/386c80a6-7752-4348-818d-88abf78ddef6

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GeometricallyIntegralIffGeometricallyConnectedOf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsIsDominantGeometricPointOfIsPreimmersion
import Theorems.Thm_GlobalTheory_genericPoints_subset_range_of_isDominant


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution {Z W : Scheme.{0}} [IrreducibleSpace W]
    (a : Z ⟶ W) [IsPreimmersion a] [IsDominant a] [QuasiCompact a] :
    ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (t : Sp k ⟶ Z), IsDominant t := by
  have hη : genericPoint W ∈ genericPoints W := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨z, hz⟩ := genericPoints_subset_range_of_isDominant a hη
  let k := AlgebraicClosure (Z.residueField z)
  let t : Sp k ⟶ Z := spMap (algebraMap (Z.residueField z) k) ≫ Z.fromSpecResidueField z
  refine ⟨k, inferInstance, inferInstance, t, ⟨fun z' => ?_⟩⟩
  have h₁ : z ⤳ z' := by
    rw [← a.isEmbedding.isInducing.specializes_iff, hz]
    exact genericPoint_specializes _
  have h₂ : z ∈ Set.range t :=
    ⟨IsLocalRing.closedPoint k, Scheme.fromSpecResidueField_apply z _⟩
  exact closure_mono (Set.singleton_subset_iff.mpr h₂) (specializes_iff_mem_closure.mp h₁)
end GlobalTheory
