-- Prove2me | solution 1 for GlobalTheory.gm_pullU_mul_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:11:52.929899+00:00
-- url     : https://prove2.me/submissions/9cfc24df-a3a0-4b9b-aed5-1d71f8500d64

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
    (le : F ⁻¹ᵁ U ≤ W) (hz : r z ∈ F ⁻¹ᵁ U) (G : Γ(X, U)ˣ) (t : Γ(Y, W)ˣ) :
    gm r z (F ⁻¹ᵁ U) (pullU F U G * res le t) = gm (r ≫ F) z U G * gm r z W t :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_pull r F z U hz G) (gm_res r z le hz t))
end GlobalTheory
