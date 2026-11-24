-- Prove2me | solution 1 for GlobalTheory.exists_isUnit_corner
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:42:39.264633+00:00
-- url     : https://prove2.me/submissions/f34455f5-b350-489d-8184-cbb6dbcbb666

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_DualRestrictSurjectiveOfIsTorsionFreeQuotient
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsIsSymplecticBasisToMatrixOffDiagDvd
import Theorems.Thm_GlobalTheory_isUnit_of_forall_maximalSpectrum_mk_ne_zero
import Theorems.Thm_GlobalTheory_exists_matrix_lift_maximalSpectrum
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
theorem _root_.solution [Finite (MaximalSpectrum R)] {A : Matrix (Unit ⊕ m) (Unit ⊕ m) R}
    (hA : IsUnit A.det) : ∃ t : Matrix Unit m R,
      IsUnit ((fromBlocks (1 : Matrix Unit Unit R) t 0 (1 : Matrix m m R) * A) (.inl ()) (.inl ())) := by
  have key : ∀ p : MaximalSpectrum R, ∃ t : Matrix Unit m (R ⧸ p.asIdeal),
      Ideal.Quotient.mk p.asIdeal (A (.inl ()) (.inl ())) +
        ∑ j, t () j * Ideal.Quotient.mk p.asIdeal (A (.inr j) (.inl ())) ≠ 0 := by
    intro p
    have := p.isMaximal
    by_cases h0 : Ideal.Quotient.mk p.asIdeal (A (.inl ()) (.inl ())) = 0
    · by_contra! hne
      have hcol : ∀ i, (A.map (Ideal.Quotient.mk p.asIdeal)) i (.inl ()) = 0 := by
        rintro (i | i)
        · exact h0
        · simpa [h0, Pi.single_apply] using hne (Matrix.of fun _ => Pi.single i 1)
      have hdet := det_eq_zero_of_column_eq_zero _ hcol
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at hdet
      exact (hA.map _).ne_zero hdet
    · exact ⟨0, by simpa using h0⟩
  choose t ht using key
  obtain ⟨T, hT⟩ := exists_matrix_lift_maximalSpectrum t
  refine ⟨T, isUnit_of_forall_maximalSpectrum_mk_ne_zero fun p => ?_⟩
  have := ht p
  rw [← hT p] at this
  simpa [Matrix.mul_apply, Fintype.sum_sum_type] using this
end GlobalTheory
