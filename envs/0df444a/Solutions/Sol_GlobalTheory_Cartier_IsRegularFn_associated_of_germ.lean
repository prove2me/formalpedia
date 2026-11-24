-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.associated_of_germ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T12:24:37.342602+00:00
-- url     : https://prove2.me/submissions/6b018770-429c-4ca9-8673-185c0e205181

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_dvd_of_germ
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_associated_of_dvd_dvd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Cartier
open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.Cartier
namespace IsRegularFn
theorem _root_.solution {U : X.Opens} {a b : Γ(X, U)} (ha : IsRegularFn a)
    (hb : IsRegularFn b)
    (h : ∀ x (hx : x ∈ U), Ideal.span {(X.presheaf.germ U x hx).hom a} =
      Ideal.span {(X.presheaf.germ U x hx).hom b}) : Associated a b :=
  ha.associated_of_dvd_dvd
    (ha.dvd_of_germ fun x hx => Ideal.span_singleton_le_span_singleton.1 (h x hx).ge)
    (hb.dvd_of_germ fun x hx => Ideal.span_singleton_le_span_singleton.1 (h x hx).le)
end IsRegularFn
end GlobalTheory.Cartier
