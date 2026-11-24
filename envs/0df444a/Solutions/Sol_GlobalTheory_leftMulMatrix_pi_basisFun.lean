-- Prove2me | solution 1 for GlobalTheory.leftMulMatrix_pi_basisFun
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T23:14:38.763951+00:00
-- url     : https://prove2.me/submissions/950a523d-5291-43f8-879f-064f42cf315e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe

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
theorem _root_.solution [DecidableEq ι] (x : ι → E) :
    leftMulMatrix (Pi.basisFun E ι) x = Matrix.diagonal x := by
  ext i j
  rw [leftMulMatrix_eq_repr_mul]
  by_cases h : i = j <;> simp [h, Matrix.diagonal_apply]
end GlobalTheory
