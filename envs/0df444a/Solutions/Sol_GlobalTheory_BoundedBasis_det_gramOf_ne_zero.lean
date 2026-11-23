-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.det_gramOf_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:58:51.208992+00:00
-- url     : https://prove2.me/submissions/b98ff266-c642-44ce-910c-56cddddf7b00

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegerApproximationCountHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_ExistsFinsetTypesOfBoundedBases
import Theorems.Thm_GlobalTheory_BoundedBasis_gramOf_eq
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
namespace GlobalTheory.BoundedBasis
theorem _root_.solution {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0)
    {v : Fin r → Fin r → E} (hv : LinearIndependent E v) : (gramOf G v).det ≠ 0 := by
  rw [gramOf_eq, det_mul, det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det]
  refine mul_ne_zero (mul_ne_zero (det_of_ne_zero hv) hG) ?_
  exact (map_ne_zero _).2 (det_of_ne_zero hv)
end GlobalTheory.BoundedBasis
