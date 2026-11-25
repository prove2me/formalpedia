-- Prove2me | solution 1 for GlobalTheory.gm_res_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:12:16.766235+00:00
-- url     : https://prove2.me/submissions/55a7acb9-b608-40b6-982f-55fbae2f312f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_res


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory
variable {Y : Scheme.{0}}
namespace GlobalTheory
theorem _root_.solution {X Z : Scheme.{0}} (r : Z ⟶ Y) (F : Y ⟶ X) (z : Z) {U : X.Opens} {W : Y.Opens}
    (le : W ≤ F ⁻¹ᵁ U) (hz : r z ∈ W) (t : Γ(X, U)ˣ) :
    gm r z W (res le (pullU F U t)) = gm (r ≫ F) z U t :=
  (gm_res r z le hz _).trans (gm_pull r F z U (le hz) t)
end GlobalTheory
