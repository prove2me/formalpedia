-- Prove2me | solution 1 for GlobalTheory.SameZeroScheme.resG_appLE
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:31:30.597791+00:00
-- url     : https://prove2.me/submissions/33301d48-429e-46dc-9d1e-9fb0775ab111

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
theorem _root_.solution {X Y : Scheme.{0}} (f : Y ⟶ X) {U : X.Opens} {V W : Y.Opens} (h : V ≤ f ⁻¹ᵁ U)
    (h' : W ≤ V) (a : Γ(X, U)) :
    resG Y h' ((f.appLE U V h).hom a) = (f.appLE U W (h'.trans h)).hom a := by
  change (f.appLE U V h ≫ Y.presheaf.map (homOfLE h').op).hom a = _
  rw [Scheme.Hom.appLE_map]
end GlobalTheory.SameZeroScheme
