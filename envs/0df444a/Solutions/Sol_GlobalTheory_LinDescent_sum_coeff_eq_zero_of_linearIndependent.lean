-- Prove2me | solution 1 for GlobalTheory.LinDescent.sum_coeff_eq_zero_of_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T18:45:03.781635+00:00
-- url     : https://prove2.me/submissions/353edd3f-d284-4b0a-9ac8-63470ce19824

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_HeckeKer
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_RigidSys
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_Splits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GtBaseChangeSt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfIsReduced
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsSmulApplyEqOfEqOnInvariants
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsDescentOfInvGenOfInvariants

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits
open TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.LinDescent
variable {X Y Z : Scheme.{0}}
namespace GlobalTheory.LinDescent
theorem _root_.solution {R M ι C : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [Fintype C] [DecidableEq ι] {v : ι → M} (hv : LinearIndependent R v) (p : C → ι)
    (a : C → R) (h : ∑ c, a c • v (p c) = 0) (i : ι) : ∑ c, (if p c = i then a c else 0) = 0 := by
  have h1 := linearIndependent_iff.1 hv (∑ c, Finsupp.single (p c) (a c)) (by
    simpa only [map_sum, Finsupp.linearCombination_single] using h)
  have h2 := DFunLike.congr_fun h1 i
  simpa only [Finsupp.finset_sum_apply, Finsupp.single_apply, Finsupp.zero_apply] using h2
end GlobalTheory.LinDescent
