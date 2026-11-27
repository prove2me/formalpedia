-- Prove2me | solution 1 for GlobalTheory.densePart_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:37:34.689222+00:00
-- url     : https://prove2.me/submissions/eed9452f-6719-42c7-a405-a85b62b478f0

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_IsIsoStalkMapOfFlatOfSurjectiveOnStalks
import Theorems.Thm_GlobalTheory_isDominant_pullback_fst_of_isOpenMap
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
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open scoped CategoryTheory.Obj TensorProduct Pointwise
namespace GlobalTheory
namespace _root_.GlobalTheory
theorem _root_.solution : ∀ (X U : Scheme.{0}) (j : U ⟶ X), IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → genericPoints X ⊆ Set.range j ∧ (∀ u : U, IsIso (j.stalkMap u)) ∧ (IsReduced X → IsSchemeTheoreticallyDominant j) ∧ ∀ (Y : Scheme.{0}) (p : Y ⟶ X), UniversallyOpen p → IsDominant (pullback.fst p j) := by
  intro X U j _ _ _ _
  refine ⟨_root_.GlobalTheory.genericPoints_subset_range_of_isDominant j,
    fun u => _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks j u,
    fun _ => (isSchemeTheoreticallyDominant_iff_isDominant j).2 inferInstance,
    fun Y p _ => _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap j p p.isOpenMap⟩
end _root_.GlobalTheory
end GlobalTheory
