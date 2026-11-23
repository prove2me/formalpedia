-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.vecMul_of
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:27:21.673317+00:00
-- url     : https://prove2.me/submissions/5781d904-1844-4a73-af70-e4f76098e7f2

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix Module
open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory
open GlobalTheory.BoundedBasis
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
omit [NumberField E] [IsCMField E]
namespace GlobalTheory.BoundedBasis
theorem _root_.solution (c : Fin r → E) (v : Fin r → Fin r → E) :
    c ᵥ* Matrix.of v = ∑ i, c i • v i := by
  ext k
  simp [vecMul, dotProduct, Finset.sum_apply]
end GlobalTheory.BoundedBasis
