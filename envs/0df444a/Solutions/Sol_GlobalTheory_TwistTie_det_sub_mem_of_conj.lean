-- Prove2me | solution 1 for GlobalTheory.TwistTie.det_sub_mem_of_conj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T21:42:23.863072+00:00
-- url     : https://prove2.me/submissions/e197a9cb-6dd0-411f-b51a-99a48f9f2212

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionFractionalIdealProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_DetSubMemOfConj
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TwistTie
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix
namespace GlobalTheory.TwistTie
theorem _root_.solution {O R : Type} [CommRing O] [CommRing R] (f : O →+* R) (A : Subring R) (hf : ∀ x, f x ∈ A)
    (I : Ideal O) (J : AddSubgroup R) (hJ : ∀ x ∈ I, ∀ y ∈ A, f x * y ∈ J) {n : ℕ} (G P Y : Matrix (Fin n) (Fin n) R)
    (a : Matrix (Fin n) (Fin n) O) (t m : O) (ht : t - 1 ∈ I) (hm : m ∈ I) (hP : IsUnit P.det) (hG : G.det ∈ A)
    (hY : ∀ i j, Y i j ∈ A) (h : (f t • G) * P = P * (a.map f + f m • Y)) : G.det - f a.det ∈ J := by
  have h1 : f t ^ n * G.det = (a.map f + f m • Y).det := by
    have := congrArg Matrix.det h
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, Fintype.card_fin, mul_comm P.det] at this
    exact hP.mul_right_cancel this
  let f' : O →+* A := f.codRestrict A hf
  let Y' : Matrix (Fin n) (Fin n) A := Matrix.of fun i j => ⟨Y i j, hY i j⟩
  have h2 : (a.map f' + f' m • Y').det - f' a.det ∈ Ideal.span {f' m} := by
    rw [← Ideal.Quotient.eq, RingHom.map_det, RingHom.map_det, RingHom.map_det]
    congr 1
    ext i j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Ideal.Quotient.eq, add_sub_cancel_left]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 h2
  have h3 := congrArg A.subtype hz
  rw [map_sub, map_mul, RingHom.map_det] at h3
  have h4 : A.subtype.mapMatrix (a.map f' + f' m • Y') = a.map f + f m • Y := by
    ext i j
    rfl
  rw [h4, ← h1] at h3
  have h5 : t ^ n - 1 ∈ I := by
    obtain ⟨q, hq⟩ := sub_dvd_pow_sub_pow t 1 n
    rw [one_pow] at hq
    rw [hq]
    exact I.mul_mem_right _ ht
  have h6 := sub_mem (hJ m hm z z.2) (hJ _ h5 _ hG)
  convert h6 using 1
  change (z : R) * f m = f t ^ n * G.det - f a.det at h3
  rw [map_sub, map_pow, map_one]
  linear_combination -h3
end GlobalTheory.TwistTie
