-- Prove2me | solution 1 for GlobalTheory.connectedSpace_of_flat_of_genericFibre
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:13:26.426391+00:00
-- url     : https://prove2.me/submissions/05b3e764-91cf-4784-b9e4-10619f45bd52

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Theorems.Thm_GlobalTheory_isDominant_genericFibre_of_flat

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
theorem _root_.solution (T K : Type) [CommRing T] [IsDomain T] [Field K]
    [Algebra T K] [IsFractionRing T K] {X : Scheme.{0}} (f : X ⟶ Sp T) [Flat f]
    [ConnectedSpace ↥(pullback f (spMap (algebraMap T K)))] : ConnectedSpace X := by
  have := isDominant_genericFibre_of_flat T K f
  let g := pullback.fst f (spMap (algebraMap T K))
  have h : _root_.IsConnected (closure (Set.range g)) := (isConnected_range g.continuous).closure
  rw [g.denseRange.closure_range] at h
  exact connectedSpace_iff_univ.mpr h
end GlobalTheory
