-- Prove2me | solution 1 for GlobalTheory.matrix_exists_left_inverse_of_forall_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T23:28:14.356006+00:00
-- url     : https://prove2.me/submissions/0902bc7a-dd96-4dbf-b8dc-64732b2c257e

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_IsCompletedStrictHens
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsLeftInverseOfFibrewiseInjective
import Theorems.Thm_GlobalTheory_matrix_exists_left_inverse_of_field

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] (m n : ℕ)
    (Q : Matrix (Fin m) (Fin n) R)
    (h : ∀ (K : Type) [Field K] (φ : R →+* K), Function.Injective (Q.map φ).mulVec) :
    ∃ Q' : Matrix (Fin n) (Fin m) R, Q' * Q = 1 := by
  let I : Ideal R :=
    { carrier := {r | ∃ L : Matrix (Fin n) (Fin m) R, L * Q = r • (1 : Matrix (Fin n) (Fin n) R)}
      add_mem' := by
        rintro a b ⟨L, hL⟩ ⟨L', hL'⟩
        exact ⟨L + L', by rw [Matrix.add_mul, hL, hL', add_smul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro c a ⟨L, hL⟩
        exact ⟨c • L, by rw [Matrix.smul_mul, hL, smul_smul, smul_eq_mul]⟩ }
  have hI : I = ⊤ := by
    by_contra hne
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hne
    letI : Field (R ⧸ p) := Ideal.Quotient.field p
    obtain ⟨Lb, hLb⟩ := matrix_exists_left_inverse_of_field _ (h (R ⧸ p) (Ideal.Quotient.mk p))
    choose s hs using Ideal.Quotient.mk_surjective (I := p)
    let L : Matrix (Fin n) (Fin m) R := Lb.map s
    have hL : L.map (Ideal.Quotient.mk p) = Lb := by
      ext i j
      simp [L, hs]
    have hdet : Ideal.Quotient.mk p (L * Q).det = 1 := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_mul, hL, hLb, Matrix.det_one]
    have hmem : (L * Q).det ∈ I :=
      ⟨(L * Q).adjugate * L, by rw [Matrix.mul_assoc, Matrix.adjugate_mul]⟩
    have h0 := Ideal.Quotient.eq_zero_iff_mem.2 (hIp hmem)
    rw [hdet] at h0
    exact one_ne_zero h0
  have h1 : (1 : R) ∈ I := by rw [hI]; trivial
  obtain ⟨L, hL⟩ := h1
  exact ⟨L, by rw [hL, one_smul]⟩
end GlobalTheory
