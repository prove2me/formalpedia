-- Prove2me | solution 1 for GlobalTheory.isIntegral_and_isNormalScheme_of_smooth_dvr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:53:31.709886+00:00
-- url     : https://prove2.me/submissions/a3a32111-154f-4ba8-b956-5227b8f66a17

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_IsIntegralAndIsNormalSchemeOfSmoothDvr
import Theorems.Thm_GlobalTheory_isIntegral_and_isNormalScheme_of_smooth

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
theorem _root_.solution :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K]
      [IsFractionRing T K] (G : Over (Sp T)), Smooth G.hom →
      ConnectedSpace ((Over.pullback (spMap (algebraMap T K))).obj G).left →
      IsIntegral G.left ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left := by
  intro T K _ _ _ _ _ _ G hG hc
  have : ConnectedSpace ↥(pullback G.hom (spMap (algebraMap T K))) := hc
  exact isIntegral_and_isNormalScheme_of_smooth T K G.hom
end GlobalTheory
