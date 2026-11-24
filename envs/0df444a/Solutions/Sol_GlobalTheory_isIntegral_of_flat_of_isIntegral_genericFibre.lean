-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_flat_of_isIntegral_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T23:03:33.80064+00:00
-- url     : https://prove2.me/submissions/d3985456-5c43-403a-84c9-835945a5903f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_BijectiveAlgebraMapIntegralClosureOfBirational
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIsoOfIsOpenImmersionOfGeometricallyConnected
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsOpenImmersionSpMapOfIsDiscreteValuationRing
import Theorems.Thm_GlobalTheory_isDominant_spMap_of_isFractionRing


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (T K : Type) [CommRing T] [IsDomain T]
    [Field K] [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [IsIntegral (pullback f (spMap (algebraMap T K)))] : IsIntegral X := by
  have := isDominant_spMap_of_isFractionRing T K
  have := IsSchemeTheoreticallyDominant.of_isDominant (spMap (algebraMap T K))
  let g := pullback.fst f (spMap (algebraMap T K))
  have : IsReduced X := IsSchemeTheoreticallyDominant.isReduced g
  have : IsDominant g := inferInstance
  have h : IsIrreducible (closure (Set.range g)) := by
    rw [← Set.image_univ]
    exact ((IrreducibleSpace.isIrreducible_univ _).image g g.continuous.continuousOn).closure
  rw [g.denseRange.closure_range] at h
  have : IrreducibleSpace X := (irreducibleSpace_def X).mpr h
  exact isIntegral_of_irreducibleSpace_of_isReduced X
end GlobalTheory
