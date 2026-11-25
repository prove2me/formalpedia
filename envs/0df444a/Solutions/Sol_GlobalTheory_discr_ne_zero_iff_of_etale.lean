-- Prove2me | solution 1 for GlobalTheory.discr_ne_zero_iff_of_etale
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T23:48:41.71194+00:00
-- url     : https://prove2.me/submissions/7ee6a114-0f3c-4902-8cd4-3d5835cf9d6d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_finite_algHom_of_isFiniteSplit
import Theorems.Thm_GlobalTheory_natCard_algHom_eq_finrank
import Theorems.Thm_GlobalTheory_det_points_sq_eq_discr
import Theorems.Thm_GlobalTheory_det_points_ne_zero_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory
theorem _root_.solution [Algebra.Etale K A] (h : Fintype.card ι = finrank K A)
    (v : ι → A) : discr K v ≠ 0 ↔ LinearIndependent K v := by
  have := FormallyUnramified.finite_of_free K A
  have := finite_algHom_of_isFiniteSplit K A (AlgebraicClosure K)
  obtain ⟨P⟩ : Nonempty (ι ≃ (A →ₐ[K] AlgebraicClosure K)) := by
    rw [← Finite.card_eq, natCard_algHom_eq_finrank, Nat.card_eq_fintype_card, h]
  rw [← det_points_ne_zero_iff P, ← pow_ne_zero_iff (a := Matrix.det _) two_ne_zero,
    det_points_sq_eq_discr]
  simp
end GlobalTheory
