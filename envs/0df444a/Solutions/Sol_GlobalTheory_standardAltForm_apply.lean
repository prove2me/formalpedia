-- Prove2me | solution 1 for GlobalTheory.standardAltForm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:19:57.886524+00:00
-- url     : https://prove2.me/submissions/527e5dfe-9146-42bf-aa82-1096066598da

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module Function
open GlobalTheory
variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
namespace GlobalTheory
theorem _root_.solution [Fintype ι] [DecidableEq ι] (d : ι → R) (x y : ι ⊕ ι → R) :
    standardAltForm d x y =
      ∑ i, d i * (x (Sum.inl i) * y (Sum.inr i) - x (Sum.inr i) * y (Sum.inl i)) := by
  simp only [standardAltForm, Matrix.toBilin'_apply, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁,
    Matrix.fromBlocks_apply₂₂, Matrix.diagonal_apply, Matrix.neg_apply, Matrix.zero_apply]
  simp only [mul_zero, zero_mul, Finset.sum_const_zero, zero_add, add_zero, mul_neg, neg_mul,
    mul_ite, ite_mul, Finset.sum_neg_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring
end GlobalTheory
