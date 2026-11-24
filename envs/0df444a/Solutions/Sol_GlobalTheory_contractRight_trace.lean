-- Prove2me | solution 1 for GlobalTheory.contractRight_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:50.68033+00:00
-- url     : https://prove2.me/submissions/3adbcce4-0b98-4d3f-bd44-7458daa5810d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Theorems.Thm_GlobalTheory_lTensor_comp_mulLeft_of_balanced
import Theorems.Thm_GlobalTheory_contractRight_apply
import Theorems.Thm_GlobalTheory_sum_contractRight_coord_tmul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory
variable {O H : Type*} [CommRing O] [CommRing H] [Algebra O H]
namespace GlobalTheory
theorem _root_.solution {ι : Type*} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) (hΘ : ∀ h : H, (h ⊗ₜ[O] (1 : H)) * Θ = ((1 : H) ⊗ₜ[O] h) * Θ) :
    contractRight Θ (Algebra.trace O H) = Algebra.TensorProduct.lmul' O Θ := by
  have htr : Algebra.trace O H = ∑ j, (b.coord j) ∘ₗ LinearMap.mulLeft O (b j) := by
    ext y
    rw [Algebra.trace_eq_matrix_trace b]
    simp [Matrix.trace, Algebra.leftMulMatrix_eq_repr_mul, mul_comm]
  have hr : ∀ (h : H) (t : H ⊗[O] O),
      TensorProduct.rid O H (h • t) = h * TensorProduct.rid O H t := by
    intro h t
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [TensorProduct.smul_tmul']
    | add x y hx hy => simp only [map_add, mul_add, smul_add, hx, hy]
  conv_rhs => rw [← sum_contractRight_coord_tmul b Θ]
  rw [htr, map_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [contractRight_apply, lTensor_comp_mulLeft_of_balanced Θ hΘ, hr, ← contractRight_apply]
  simp [mul_comm]
end GlobalTheory
