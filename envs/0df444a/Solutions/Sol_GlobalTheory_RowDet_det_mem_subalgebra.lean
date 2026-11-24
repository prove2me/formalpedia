-- Prove2me | solution 1 for GlobalTheory.RowDet.det_mem_subalgebra
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T20:07:13.148811+00:00
-- url     : https://prove2.me/submissions/faad6338-f3dc-450e-ad4b-76dfbd66a1e6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_IrreducibleDetOfIsRelPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.RowDet
namespace GlobalTheory.RowDet
theorem _root_.solution {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    {m : Type*} [Fintype m] [DecidableEq m] (S : Subalgebra R A) (M : Matrix m m A)
    (h : ∀ i j, M i j ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  exact S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)
end GlobalTheory.RowDet
