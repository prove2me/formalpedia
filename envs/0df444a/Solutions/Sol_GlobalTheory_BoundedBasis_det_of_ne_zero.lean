-- Prove2me | solution 1 for GlobalTheory.BoundedBasis.det_of_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:33.913064+00:00
-- url     : https://prove2.me/submissions/571214a2-07f9-48f2-878e-d387752dd728

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
theorem _root_.solution {v : Fin r → Fin r → E} (hv : LinearIndependent E v) :
    (Matrix.of v).det ≠ 0 :=
  ((Matrix.isUnit_iff_isUnit_det _).1
    ((Matrix.linearIndependent_rows_iff_isUnit (A := Matrix.of v)).1 hv)).ne_zero
end GlobalTheory.BoundedBasis
