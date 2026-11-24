-- Prove2me | solution 1 for GlobalTheory.CentralIdemIntegral.trace_leftMulMatrix
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T12:09:30.930339+00:00
-- url     : https://prove2.me/submissions/f7017a46-5af0-4bd4-9d32-fec856462dbd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open GlobalTheory GlobalTheory.CentralIdemIntegral
namespace GlobalTheory.CentralIdemIntegral
theorem _root_.solution {G K : Type} [Group G] [Fintype G] [DecidableEq G] [Field K]
    (x : MonoidAlgebra K G) :
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)).trace = (Fintype.card G : K) * x.coeff 1 := by

  have hdiag : ∀ g : G, (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K)
      (Algebra.lmul K (MonoidAlgebra K G) x)) g g = x.coeff 1 := by
    intro g
    rw [LinearMap.toMatrixAlgEquiv_apply]
    change (x * MonoidAlgebra.single g 1).coeff g = x.coeff 1
    rw [MonoidAlgebra.coeff_mul_single_apply, mul_inv_cancel, mul_one]
  rw [Matrix.trace]
  simp only [Matrix.diag, hdiag, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
end GlobalTheory.CentralIdemIntegral
