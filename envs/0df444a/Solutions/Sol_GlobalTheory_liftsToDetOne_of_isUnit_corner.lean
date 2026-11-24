-- Prove2me | solution 1 for GlobalTheory.liftsToDetOne_of_isUnit_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T23:24:47.463798+00:00
-- url     : https://prove2.me/submissions/6cbed675-ac6f-4ead-85d7-71d78d14bd93

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_LiftsToDetOne_det_eq
import Theorems.Thm_GlobalTheory_LiftsToDetOne_of_mul_left
import Theorems.Thm_GlobalTheory_LiftsToDetOne_transvection
import Theorems.Thm_GlobalTheory_liftsToDetOne_of_corner_eq_one
import Theorems.Thm_GlobalTheory_orthogonalQuotientForm_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.orthogonalQuotientForm_mk



set_option autoImplicit false
open Matrix Module Function
open private exists_symmetric_X_invertible_add_mul_of_ker_inter_eq_bot from
  Mathlib.LinearAlgebra.SymplecticGroup
open GlobalTheory
variable {S R : Type*} [CommRing S] [CommRing R] {f : S →+* R}
  {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
namespace GlobalTheory
theorem _root_.solution (hf : Surjective f)
    (ih : ∀ D : Matrix m m R, D.det = 1 → LiftsToDetOne f D)
    {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R} (hA : A.det = 1)
    (h1 : IsUnit (A (.inl ()) (.inl ()))) : LiftsToDetOne f A := by
  rcases isEmpty_or_nonempty m with hm | ⟨⟨j⟩⟩
  · refine liftsToDetOne_of_corner_eq_one hf ih hA ?_
    have : Subsingleton (Unit ⊕ m) := ⟨by rintro (i | i) (j | j) <;> first | rfl | exact hm.elim ‹_›⟩
    rw [← hA, det_eq_elem_of_subsingleton A (.inl ())]
  obtain ⟨a, ha⟩ := h1.exists_left_inv
  have e₁ := LiftsToDetOne.transvection (i := (.inr j : Unit ⊕ m)) (j := .inl ()) hf (by simp)
    ((1 - A (.inr j) (.inl ())) * a)
  have e₂ := LiftsToDetOne.transvection (i := (.inl () : Unit ⊕ m)) (j := .inr j) hf (by simp)
    (1 - A (.inl ()) (.inl ()))
  refine e₁.of_mul_left (e₂.of_mul_left (liftsToDetOne_of_corner_eq_one hf ih ?_ ?_))
  · rw [det_mul, det_mul, e₁.det_eq, e₂.det_eq, hA, one_mul, one_mul]
  · rw [transvection_mul_apply_same, transvection_mul_apply_same,
      transvection_mul_apply_of_ne _ _ _ _ (by simp), mul_assoc, ha]
    ring
end GlobalTheory
