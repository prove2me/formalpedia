-- Prove2me | solution 1 for GlobalTheory.RootUnit.gs_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:07:20.151819+00:00
-- url     : https://prove2.me/submissions/25adefa5-28c1-45c0-8ae8-bbb50ab26e58

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_CubeVal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_IsNsmul
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_QkToAkU
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_ExistsUnitOfStalks
import Theorems.Thm_GlobalTheory_RootUnit_gs_id

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.RootUnit
open TopologicalSpace
namespace GlobalTheory.RootUnit
theorem _root_.solution {Y : Scheme.{0}} [IsIntegral Y] (y : Y) (U : Y.Opens) (h : y ∈ U) {a : Γ(Y, U)} (ha : a ≠ 0) :
    gs (𝟙 Y) y U a ≠ 0 := by
  rw [gs_id y U h]
  intro e
  exact ha (germ_injective_of_isIntegral Y y h (e.trans (map_zero _).symm))
end GlobalTheory.RootUnit
