-- Prove2me | solution 1 for GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:16:20.885154+00:00
-- url     : https://prove2.me/submissions/a2a34b36-9703-4606-adcb-c0a0248ca2fd

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SemiabelianSchemes_PrecompleteBases_PsbLb
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_NonzeroLocus
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsGrpPullback
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ThetaUnifAV
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_IsRegularFnIffOfIsAffineOpen
import Theorems.Thm_GlobalTheory_Cartier_IsRegularFn_mem
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
theorem _root_.solution {U : X.Opens} (hU : IsAffineOpen U) {a : Γ(X, U)} :
    IsRegularFn a ↔ a ∈ nonZeroDivisors Γ(X, U) := by
  refine ⟨IsRegularFn.mem, fun ha => isRegularFn_iff_germ.2 fun x hx => ?_⟩
  letI : Algebra Γ(X, U) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  exact IsLocalization.nonZeroDivisors_le_comap (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (X.presheaf.stalk x) ha
end GlobalTheory.Cartier
