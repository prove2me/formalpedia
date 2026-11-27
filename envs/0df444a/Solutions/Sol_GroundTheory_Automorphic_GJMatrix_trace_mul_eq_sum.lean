-- Prove2me | solution 1 for GroundTheory.Automorphic.GJMatrix.trace_mul_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:43:06.422242+00:00
-- url     : https://prove2.me/submissions/0749f6c1-94f1-4899-9a3e-5813e4798f4a

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixInfinite
import Definitions.Def_GroundTheory_AutomorphicForms_GL2_GJMatrixCoord

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open MeasureTheory Matrix
noncomputable section
variable {n X : Type*} [Fintype n]
namespace GroundTheory.Automorphic.GJMatrix
theorem _root_.solution {R : Type*} [CommRing R] (x y : Matrix n n R) :
    trace (x * y) = ∑ p, matrixCoord x p * matrixCoordT y p := by
  rw [trace, Fintype.sum_prod_type]
  simp only [diag_apply, mul_apply, matrixCoord, matrixCoordT]
end GroundTheory.Automorphic.GJMatrix
