-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.appLE_resG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:27.460846+00:00
-- url     : https://prove2.me/submissions/85285670-897a-4ca6-b78c-a3824770f965

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_ExistsUnitMul
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_IsoLineBundleOfRegularPullbacksSameZeroScheme

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
open GlobalTheory GlobalTheory.SameZeroScheme
namespace GlobalTheory.SameZeroScheme
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {U U' : X.Opens} {V : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : U ≤ U') (h'' : V ≤ f ⁻¹ᵁ U') (a : Γ(X, U')) :
    (f.appLE U V h).hom (resG X h' a) = (f.appLE U' V h'').hom a := by
  change (X.presheaf.map (homOfLE h').op ≫ f.appLE U V h).hom a = _
  rw [Scheme.Hom.map_appLE]
end GlobalTheory.SameZeroScheme
