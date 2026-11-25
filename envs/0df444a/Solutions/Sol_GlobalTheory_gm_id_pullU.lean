-- Prove2me | solution 1 for GlobalTheory.gm_id_pullU
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:13:16.456998+00:00
-- url     : https://prove2.me/submissions/fb79494d-46dc-4201-b186-41399e264eda

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsHolPeriods
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CubicalLineBundles_NonemptyIsLimitBaseChange
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_LBIso_trans
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_Tor_gm_pull


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
theorem _root_.solution {X : Scheme.{0}} (F : Y ⟶ X) (y : Y) (U : X.Opens) (hy : F y ∈ U) (t : Γ(X, U)ˣ) :
    gm (𝟙 Y) y (F ⁻¹ᵁ U) (pullU F U t) = gm F y U t :=
  (gm_pull (𝟙 Y) F y U hy t).trans (by rw [Category.id_comp])
end GlobalTheory
