-- Prove2me | solution 1 for GlobalTheory.GenIsoRatio.gm_pullU_res
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T16:33:02.977712+00:00
-- url     : https://prove2.me/submissions/3fa2d30b-e1a7-4503-b887-f6b5920a2eec

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AbelianSchemeLaws_FirstCohomologyVanishesSpecOfIsLocalRing
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_RigidifiedPartialLineBundleIsoCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsGlobalUnitRatioGenericLineBundleIsos
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
open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
noncomputable section
open GlobalTheory GlobalTheory.GenIsoRatio
namespace GlobalTheory.GenIsoRatio
theorem _root_.solution {X Y : Scheme.{0}} (β : Y ⟶ X) (U : X.Opens) {V : Y.Opens} (h : V ≤ β ⁻¹ᵁ U) (y : Y)
    (hy : y ∈ V) (a : Γ(X, U)ˣ) : gm (𝟙 Y) y V (res h (pullU β U a)) = gm β y U a := by
  rw [gm_res (𝟙 Y) y h hy, gm_pull (𝟙 Y) β y U (h hy), Category.id_comp]
end GlobalTheory.GenIsoRatio
