-- Prove2me | solution 1 for GlobalTheory.IsSymplecticBasis.bijective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:21:21.962546+00:00
-- url     : https://prove2.me/submissions/006a1894-0210-4fe6-a1ab-cfbd93914ddb

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticFamily_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasisOfType_apply_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_left_right
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_right_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_left
import Theorems.Thm_GlobalTheory_IsSymplecticBasis_apply_right

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
  {B : LinearMap.BilinForm R M}
open GlobalTheory.IsSymplecticBasis
variable {b : Basis (ι ⊕ ι) R M}
namespace GlobalTheory.IsSymplecticBasis
theorem _root_.solution [Finite ι] (h : IsSymplecticBasis B b) (hB : B.IsAlt) : Bijective B := by
  classical
  have := Fintype.ofFinite ι
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    refine b.ext_elem fun i => ?_
    rcases i with i | i
    · simp [← h.apply_right, hx]
    · simp [← h.apply_left, ← hB.neg_eq x, hx]
  · intro φ
    refine ⟨∑ i, (φ (b (Sum.inr i)) • b (Sum.inl i) - φ (b (Sum.inl i)) • b (Sum.inr i)),
      b.ext fun j => ?_⟩
    rcases j with j | j
    · simp [h.left_left, h.right_left hB]
    · simp [h.right_right, h.left_right]
end GlobalTheory.IsSymplecticBasis
