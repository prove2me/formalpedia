-- Prove2me | solution 1 for GlobalTheory.det_points_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:41:17.932485+00:00
-- url     : https://prove2.me/submissions/045b9c5c-b28f-4439-b44a-977eb48315b4

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
import Theorems.Thm_GlobalTheory_card_eq_finrank_of_points
import Theorems.Thm_GlobalTheory_det_points_sq_eq_discr
import Theorems.Thm_GlobalTheory_det_points_ne_zero_of_basis

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
theorem _root_.solution {E : Type*} [Field E] [Algebra K E] [Module.Finite K A]
    [IsFiniteSplit E (E ⊗[K] A)] (P : ι ≃ (A →ₐ[K] E)) (v : ι → A) :
    (Matrix.of fun i j ↦ P j (v i)).det ≠ 0 ↔ LinearIndependent K v := by
  constructor
  · intro h
    by_contra hli
    have := det_points_sq_eq_discr P v
    rw [discr_zero_of_not_linearIndependent K hli, map_zero] at this
    exact pow_ne_zero 2 h this
  · intro h
    simpa using det_points_ne_zero_of_basis P
      (basisOfLinearIndependentOfCardEqFinrank' v h (card_eq_finrank_of_points P))
end GlobalTheory
