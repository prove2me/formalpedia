-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.exists_vecMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:52.652506+00:00
-- url     : https://prove2.me/submissions/34e3d356-4ea1-4660-855b-1546c92c65ca

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_det_of_ne_zero

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
theorem _root_.solution {v : Fin r → Fin r → E} (hv : LinearIndependent E v) (x : Fin r → E) :
    ∃ c, x = c ᵥ* Matrix.of v :=
  ⟨x ᵥ* (Matrix.of v)⁻¹, by
    rw [vecMul_vecMul, nonsing_inv_mul _ (det_of_ne_zero hv).isUnit, vecMul_one]⟩
end GlobalTheory.BoundedBasis
