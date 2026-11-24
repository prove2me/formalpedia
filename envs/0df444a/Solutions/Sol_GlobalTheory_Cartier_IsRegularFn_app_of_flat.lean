-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.app_of_flat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T12:09:27.351806+00:00
-- url     : https://prove2.me/submissions/9ae69f76-8b5b-4cbf-8f07-cd29ee2970ad

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_iff_germ

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
theorem _root_.solution (φ : Y ⟶ X) [Flat φ] {U : X.Opens} {a : Γ(X, U)}
    (ha : IsRegularFn a) : IsRegularFn ((φ.app U).hom a) := by
  refine isRegularFn_iff_germ.2 fun y hy => ?_
  let _ := (φ.stalkMap y).hom.toAlgebra
  have : Module.Flat (X.presheaf.stalk (φ y)) (Y.presheaf.stalk y) := Flat.stalkMap φ y
  have h1 := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Y.presheaf.stalk y)
    (isRegularFn_iff_germ.1 ha (φ y) hy)
  have e := Scheme.Hom.germ_stalkMap_apply φ U y hy a
  refine mem_nonZeroDivisors_iff_left.2 fun t ht => h1 ?_
  change (φ.stalkMap y).hom _ * t = (φ.stalkMap y).hom _ * 0
  rw [mul_zero]
  exact (congrArg (· * t) e).trans ht
end IsRegularFn
end GlobalTheory.Cartier
