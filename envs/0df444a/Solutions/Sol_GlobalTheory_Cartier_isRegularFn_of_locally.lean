-- Prove2me | solution 1 for GlobalTheory.Cartier.isRegularFn_of_locally
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:08:36.034803+00:00
-- url     : https://prove2.me/submissions/8fb944ae-b6cd-4373-82ea-f4de1882eeb4

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
theorem _root_.solution {U : X.Opens} {a : Γ(X, U)}
    (h : ∀ x ∈ U, ∃ (V : X.Opens) (hV : V ≤ U), x ∈ V ∧ IsRegularFn (resG X hV a)) :
    IsRegularFn a := by
  refine isRegularFn_iff_germ.2 fun x hx => ?_
  obtain ⟨V, hV, hxV, hr⟩ := h x hx
  have := isRegularFn_iff_germ.1 hr x hxV
  rwa [germ_resG] at this
end GlobalTheory.Cartier
