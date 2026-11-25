-- Prove2me | solution 1 for GlobalTheory.isIntegral_of_isAbelianScheme_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:58:05.85844+00:00
-- url     : https://prove2.me/submissions/fd8ccc2d-13ec-4197-bd6a-498ce09f465b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_SecBaseChangeAnySt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsIntegralOfSmoothFieldOfConnectedSpace
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaFamilyOrigin_IsIntegralOfIsAbelianSchemeField
import Theorems.Thm_GlobalTheory_geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) : IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton A.hom
end GlobalTheory
