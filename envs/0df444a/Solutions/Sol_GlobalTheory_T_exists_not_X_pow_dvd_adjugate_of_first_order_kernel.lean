-- Prove2me | solution 1 for GlobalTheory.T.exists_not_X_pow_dvd_adjugate_of_first_order_kernel
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T22:55:40.745356+00:00
-- url     : https://prove2.me/submissions/6ca78b81-0f66-4d55-ae58-a11336cc2274

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsNotXPowDvdAdjugateOfFirstOrderKernelStatement
import Theorems.Thm_GlobalTheory_exists_not_X_pow_dvd_adjugate_of_firstOrderKernel


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
theorem _root_.solution : ∀ (K : Type) [Field K] (a m : ℕ) (Ψ : Matrix (Fin a) (Fin a) (Polynomial K)), (∀ x0 x1 : Fin (1 + 1) → Fin a → K, (∀ j, (Ψ.map fun p => p.coeff 0).mulVec (x0 j) = 0 ∧ (Ψ.map fun p => p.coeff 1).mulVec (x0 j) + (Ψ.map fun p => p.coeff 0).mulVec (x1 j) = 0) → ¬ LinearIndependent K x0) → Module.finrank K (LinearMap.ker (Ψ.map fun p => p.coeff 0).mulVecLin) ≤ m + 1 → a ≠ 0 → ∃ b c, ¬ (Polynomial.X : Polynomial K) ^ (2 * m + 1) ∣ Ψ.adjugate b c := by
  first | exact @GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | exact GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel | (intros; apply GlobalTheory.exists_not_X_pow_dvd_adjugate_of_firstOrderKernel <;> assumption)
end _root_.GlobalTheory.T
