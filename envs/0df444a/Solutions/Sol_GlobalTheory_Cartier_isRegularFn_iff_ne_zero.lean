-- Prove2me | solution 1 for GlobalTheory.Cartier.isRegularFn_iff_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:36:19.572771+00:00
-- url     : https://prove2.me/submissions/d6a184a4-a677-4521-8abd-03f34490f74d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_isRegularFn_of_ne_zero
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_ne_zero

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
theorem _root_.solution [IsIntegral X] {U : X.Opens} [Nonempty U] {a : Γ(X, U)} :
    IsRegularFn a ↔ a ≠ 0 :=
  ⟨IsRegularFn.ne_zero, isRegularFn_of_ne_zero⟩
end GlobalTheory.Cartier
