-- Prove2me | solution 1 for GlobalTheory.sum_contractRight_coord_tmul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:58.872112+00:00
-- url     : https://prove2.me/submissions/7e2e503b-6929-426a-b6a1-9f189463b9b3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_DvdTraceOfBalancedTensor
import Theorems.Thm_GlobalTheory_contractRight_apply

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
theorem _root_.solution {ι : Type*} [Fintype ι] (b : Module.Basis ι O H)
    (Θ : H ⊗[O] H) : ∑ j, contractRight Θ (b.coord j) ⊗ₜ[O] b j = Θ := by
  induction Θ using TensorProduct.induction_on with
  | zero => simp [contractRight_apply]
  | tmul x y =>
    simp only [contractRight_apply, LinearMap.lTensor_tmul, TensorProduct.rid_tmul,
      TensorProduct.smul_tmul, ← TensorProduct.tmul_sum, Module.Basis.coord_apply, b.sum_repr]
  | add x y hx hy =>
    simp only [contractRight_apply, map_add, TensorProduct.add_tmul, Finset.sum_add_distrib] at *
    rw [hx, hy]
end GlobalTheory
