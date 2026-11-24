-- Prove2me | solution 1 for GlobalTheory.T.not_X_pow_succ_dvd_det_of_first_order_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:35:25.319797+00:00
-- url     : https://prove2.me/submissions/9a5b7807-abfb-4eb7-8741-10177271a5dc

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NotXPowSuccDvdDetOfFirstOrderKernelEqZeroStatement
import Theorems.Thm_GlobalTheory_not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (0 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m → ¬ (Polynomial.X : Polynomial K) ^ (m + 1) ∣ Ψ.det := by
  first | exact @GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | exact GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero | (intros; apply GlobalTheory.not_X_pow_succ_dvd_det_of_first_order_kernel_eq_zero <;> assumption)
end _root_.GlobalTheory.T
