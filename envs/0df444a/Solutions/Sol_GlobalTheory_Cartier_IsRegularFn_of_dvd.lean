-- Prove2me | solution 1 for GlobalTheory.Cartier.IsRegularFn.of_dvd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T09:41:38.488631+00:00
-- url     : https://prove2.me/submissions/0900cb63-1eeb-4445-a934-835b7654bae5

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen

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
open GlobalTheory.Cartier.IsRegularFn
variable {U : X.Opens} {a b : Γ(X, U)}
namespace GlobalTheory.Cartier.IsRegularFn
theorem _root_.solution (hb : IsRegularFn b) (h : a ∣ b) : IsRegularFn a := fun W hW => by
  obtain ⟨c, rfl⟩ := h
  have := hb W hW
  rw [map_mul] at this
  exact (mul_mem_nonZeroDivisors.1 this).1
end GlobalTheory.Cartier.IsRegularFn
