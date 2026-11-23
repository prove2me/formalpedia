-- Prove2me | solution 1 for GlobalTheory.Capelli.cross_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T12:52:33.841853+00:00
-- url     : https://prove2.me/submissions/29d44d85-3962-4720-ac7c-7b666d116266

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
import Theorems.Thm_P2M_GlobalTheory_Capelli_pderiv_X_mul__2a5262d9a5e3
import Theorems.Thm_GlobalTheory_Capelli_polar_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Capelli.polar_apply

set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
namespace GlobalTheory.Capelli
theorem _root_.solution {K σ : Type*} [CommRing K] {p q n : ℕ} (z : Fin p × Fin n → σ)
    (y : Fin q × Fin n → σ) (hzy : ∀ u w, z u ≠ y w) (P : MvPolynomial σ K) :
    (∑ k, ∑ l, ∑ a, X (z (a, k)) * pderiv (z (a, l))
        (∑ b, X (y (b, k)) * pderiv (y (b, l)) P)) =
      ∑ a, ∑ b, (∑ k, X (z (a, k)) * X (y (b, k))) *
        ∑ l, pderiv (z (a, l)) (pderiv (y (b, l)) P) := by
  classical
  simp only [map_sum, pderiv_X_mul', if_neg (hzy _ _), add_zero, Finset.mul_sum, Finset.sum_mul]
  calc _ = ∑ k, ∑ a, ∑ b, ∑ l, X (z (a, k)) * (X (y (b, k)) *
            pderiv (z (a, l)) (pderiv (y (b, l)) P)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = _ := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [Finset.sum_comm]
        simp only [mul_assoc]
end GlobalTheory.Capelli
