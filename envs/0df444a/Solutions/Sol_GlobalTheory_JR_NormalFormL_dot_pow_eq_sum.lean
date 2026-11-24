-- Prove2me | solution 1 for GlobalTheory.JR.NormalFormL.dot_pow_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T18:08:32.76241+00:00
-- url     : https://prove2.me/submissions/d8542a0f-5bce-43d0-8da2-4e83774ae6aa

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_FourierMatch
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisBorderedMatrixNormalFormInvariants
import Theorems.Thm_P2M_GlobalTheory_JR_NormalFormL_sum_mulVec__fc8d7b839a0b

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.NormalFormL
variable {k : Type} [Field k] {r : ℕ}
namespace GlobalTheory.JR.NormalFormL
theorem _root_.solution (M : Matrix (Fin r) (Fin r) k) (hr : 0 < r) (b c : Fin r → k) (n : ℕ) :
    c ⬝ᵥ (M ^ n *ᵥ b) = ∑ i ∈ Finset.range r,
      ((Polynomial.X ^ n) %ₘ M.charpoly).coeff i * (c ⬝ᵥ (M ^ i *ᵥ b)) := by
  have hmon := charpoly_monic M
  have hdeg : M.charpoly.natDegree = r := by simp
  have hne : M.charpoly ≠ 1 := by
    intro h; rw [h, Polynomial.natDegree_one] at hdeg; omega
  have hM : M ^ n = Polynomial.aeval M ((Polynomial.X ^ n) %ₘ M.charpoly) := by
    rw [Polynomial.aeval_modByMonic_eq_self_of_root (aeval_self_charpoly M)]
    simp
  rw [hM, Polynomial.aeval_eq_sum_range' (n := r)
    (by have := Polynomial.natDegree_modByMonic_lt (Polynomial.X ^ n) hmon hne; omega), sum_mulVec', dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul]
end GlobalTheory.JR.NormalFormL
