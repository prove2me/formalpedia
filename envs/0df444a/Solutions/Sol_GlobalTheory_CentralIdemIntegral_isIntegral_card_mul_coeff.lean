-- Prove2me | solution 1 for GlobalTheory.CentralIdemIntegral.isIntegral_card_mul_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:39:23.204805+00:00
-- url     : https://prove2.me/submissions/e750f622-512e-43df-b01c-5c4974fc1040

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_CardMulCoeffMem
import Theorems.Thm_GlobalTheory_CentralIdemIntegral_isIntegral_trace
import Theorems.Thm_GlobalTheory_CentralIdemIntegral_trace_leftMulMatrix

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
theorem _root_.solution {G K : Type} [Group G] [Fintype G] [Field K] [CharZero K]
    (e : MonoidAlgebra K G) (he : e * e = e) (hc : ∀ x, e * x = x * e) (g : G) :
    IsIntegral ℤ ((Fintype.card G : K) * e.coeff g) := by
  classical

  set y : MonoidAlgebra K G := e * MonoidAlgebra.single g⁻¹ 1 with hy
  have hcoeff : y.coeff 1 = e.coeff g := by
    rw [hy, MonoidAlgebra.coeff_mul_single_apply, one_mul, inv_inv, mul_one]
  have hidem : IsIdempotentElem e := he
  have hypow : y ^ (Fintype.card G + 1) = y := by
    rw [hy, (show Commute e (MonoidAlgebra.single g⁻¹ 1) from hc _).mul_pow, hidem.pow_succ_eq,
      MonoidAlgebra.single_pow, one_pow, pow_succ, pow_card_eq_one, one_mul]
  have hM := isIntegral_trace
    (LinearMap.toMatrixAlgEquiv (MonoidAlgebra.basis G K) (Algebra.lmul K (MonoidAlgebra K G) y))
    (n := Fintype.card G) Fintype.card_ne_zero (by rw [← map_pow, ← map_pow, hypow])
  rw [trace_leftMulMatrix, hcoeff] at hM
  exact hM
end GlobalTheory.CentralIdemIntegral
