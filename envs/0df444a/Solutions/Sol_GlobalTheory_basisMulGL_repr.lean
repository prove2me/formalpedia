-- Prove2me | solution 1 for GlobalTheory.basisMulGL_repr
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:36:09.993472+00:00
-- url     : https://prove2.me/submissions/8bceb6ce-d65a-4dc5-8dad-0c23ad0594a1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_ExistsIsAdaptedOfIsLocalRing

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module TensorProduct
open GlobalTheory
noncomputable section
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution (b : Basis ι R M) (g : GL ι R) (x : M) (i : ι) :
    (basisMulGL b g).repr x i = ∑ j, ((g⁻¹ : GL ι R) : Matrix ι ι R) i j * b.repr x j := by
  have h : basisMulGL (basisMulGL b g) g⁻¹ = b := by rw [← basisMulGL_mul]; simp
  have h' : (basisMulGL b g).toMatrix b = ((g⁻¹ : GL ι R) : Matrix ι ι R) := by
    conv_lhs => rw [← h]
    rw [h, ← toMatrix_basisMulGL (basisMulGL b g) g⁻¹, h]
  rw [← h']
  conv_lhs => rw [← b.sum_repr x]
  simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Basis.toMatrix_apply, mul_comm]
end GlobalTheory
