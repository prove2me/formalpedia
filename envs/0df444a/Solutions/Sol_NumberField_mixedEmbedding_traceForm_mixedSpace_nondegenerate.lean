-- Prove2me | solution 1 for NumberField.mixedEmbedding.traceForm_mixedSpace_nondegenerate
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/303f4228-1a7f-5e2a-b593-82f0cb132f7f

import Theorems.Thm_NumberField_mixedEmbedding_trace_mixedEmbedding
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding Module
open scoped Classical

theorem solution
    (K : Type*) [Field K] [NumberField K] :
    (Algebra.traceForm ℝ (mixedSpace K)).Nondegenerate := by
  apply LinearMap.BilinForm.nondegenerate_of_det_ne_zero _ (latticeBasis K)
  have h : LinearMap.BilinForm.toMatrix (latticeBasis K) (Algebra.traceForm ℝ (mixedSpace K))
      = (Algebra.traceMatrix ℚ (integralBasis K)).map (algebraMap ℚ ℝ) := by
    ext i j
    rw [Algebra.traceForm_toMatrix, Matrix.map_apply, Algebra.traceMatrix_apply,
      latticeBasis_apply, latticeBasis_apply, ← map_mul, NumberField.mixedEmbedding.trace_mixedEmbedding,
      Algebra.traceForm_apply, eq_ratCast]
  rw [h, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← Algebra.discr_def, map_ne_zero]
  exact Algebra.discr_not_zero_of_basis ℚ (integralBasis K)

end S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate
end P2MW
export P2MW.S_NumberField_mixedEmbedding_traceForm_mixedSpace_nondegenerate (solution)
