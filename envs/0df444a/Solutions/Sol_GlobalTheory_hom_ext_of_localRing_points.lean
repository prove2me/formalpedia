-- Prove2me | solution 1 for GlobalTheory.hom_ext_of_localRing_points
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T09:31:52.768651+00:00
-- url     : https://prove2.me/submissions/e4a1d554-dc0a-439e-8862-8c05703c212c

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_MulLeftCompOfPullbackPointEquivMul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_HomExtOfLocalRingPoints
import Theorems.Thm_GlobalTheory_hom_ext_of_fromSpecStalk


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution :
    ∀ (X Y : Scheme.{0}) (f g : X ⟶ Y),
      (∀ (A : Type) [CommRing A] [IsLocalRing A] (t : Sp A ⟶ X), t ≫ f = t ≫ g) → f = g :=
  fun X _ _ _ h => hom_ext_of_fromSpecStalk fun x =>
    @h (X.presheaf.stalk x) _ (X.toLocallyRingedSpace.isLocalRing x) (X.fromSpecStalk x)
end GlobalTheory
