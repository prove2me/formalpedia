-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_densePart
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:32.557832+00:00
-- url     : https://prove2.me/submissions/208fdc6b-55c7-4c77-9f0f-d5fcc790907d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsUniqueLiftSpecOfIsLocalizationAway
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueLiftOfDensePart
import Theorems.Thm_GlobalTheory_genericPoints_subset_range_of_isDominant
import Theorems.Thm_GlobalTheory_isIso_stalkMap_of_flat_of_surjectiveOnStalks


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
theorem _root_.solution {T U : Scheme.{0}} (j : U ⟶ T) [IsIntegral T]
    [GlobalTheory.IsNormalScheme T] [IsPreimmersion j] [Flat j] [IsDominant j] [QuasiCompact j] :
    IsIntegral U := by
  have := isIso_stalkMap_of_flat_of_surjectiveOnStalks j
  have : GlobalTheory.IsNormalScheme U := GlobalTheory.IsNormalScheme.of_isIso_stalkMap j
  have hη : genericPoint T ∈ genericPoints T := by
    rw [genericPoints_eq_singleton]; rfl
  obtain ⟨u, hu⟩ := genericPoints_subset_range_of_isDominant j hη
  have hgen : IsGenericPoint u (Set.univ : Set U) := by
    rw [isGenericPoint_iff_specializes]
    refine fun y => ⟨fun _ => trivial, fun _ => ?_⟩
    rw [← j.isEmbedding.isInducing.specializes_iff, hu]
    exact (genericPoint_spec T).specializes trivial
  have : IrreducibleSpace U := by
    rw [irreducibleSpace_def]
    exact hgen.isIrreducible
  exact GlobalTheory.IsNormalScheme.isIntegral_of_irreducibleSpace U
end GlobalTheory
