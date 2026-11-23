-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:07:49.286889+00:00
-- url     : https://prove2.me/submissions/c43996d5-3e59-41f9-99c5-a4e37bf7f2d1

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
theorem _root_.solution {U : X.Opens} [hU : Nonempty U] {a : Γ(X, U)} (ha : IsRegularFn a) :
    a ≠ 0 := by
  obtain ⟨⟨x, hx⟩⟩ := hU
  rintro rfl
  have := isRegularFn_iff_germ.1 ha x hx
  rw [map_zero] at this
  exact zero_notMem_nonZeroDivisors this
end IsRegularFn
end GlobalTheory.Cartier
