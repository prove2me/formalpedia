-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.herm_eq_dotProduct
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:57:00.725048+00:00
-- url     : https://prove2.me/submissions/50589445-5e45-4cdd-9fe5-4aeb0466c707

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
namespace GlobalTheory.BoundedBasis
theorem _root_.solution (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = (x ᵥ* G) ⬝ᵥ fun b => cc (y b) := by
  simp only [herm, vecMul, dotProduct, Finset.sum_mul]
  exact Finset.sum_comm
end GlobalTheory.BoundedBasis
