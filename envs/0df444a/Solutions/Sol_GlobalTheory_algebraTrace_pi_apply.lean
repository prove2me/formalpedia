-- Prove2me | solution 1 for GlobalTheory.algebraTrace_pi_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:19:58.517014+00:00
-- url     : https://prove2.me/submissions/f8023699-7a3d-4870-80ba-4cc4d545c1fd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_leftMulMatrix_pi_basisFun

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]
namespace GlobalTheory
theorem _root_.solution (x : ι → E) : Algebra.trace E (ι → E) x = ∑ i, x i := by
  classical
  rw [Algebra.trace_eq_matrix_trace (Pi.basisFun E ι), leftMulMatrix_pi_basisFun,
    Matrix.trace_diagonal]
end GlobalTheory
