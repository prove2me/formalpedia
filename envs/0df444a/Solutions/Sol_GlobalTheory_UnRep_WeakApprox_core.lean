-- Prove2me | solution 1 for GlobalTheory.UnRep.WeakApprox.core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T22:01:56.444379+00:00
-- url     : https://prove2.me/submissions/79f7168c-373b-44ce-91f0-f7ce99f33dcf

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermForm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_CayleyTransformUnitarySkewInvolutiveStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IdempotentAdelesAndSmallAdelicMatricesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_AdelicUnitaryScalingUnitStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsInverseOneAddPreservingAdelicCompletionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsRationalMatrixApproxAdeleLinearMapStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_UnitaryGroupWeakApproximationAtPrimes
import Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_inv__258392d9c0ad
import Theorems.Thm_P2M_GlobalTheory_UnRep_WeakApprox_map_smul___9facef897ec7
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_idem_factor
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_idem_diff
import Theorems.Thm_GlobalTheory_UnRep_WeakApprox_preserves_form_smul_idempotent_glue
import Theorems.Thm_GlobalTheory_Idele_adelicMulEquiv_mk
import Theorems.Thm_GlobalTheory_T_cayleyTransform_unitary_skew_involutive
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] GlobalTheory.Idele.adelicMulEquiv_mk



set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix
open GlobalTheory GlobalTheory.UnRep GlobalTheory.UnRep.WeakApprox
namespace GlobalTheory.UnRep.WeakApprox
theorem _root_.solution {K R : Type} [Field K] [CommRing R] (ι : K →+* R) (c : K →+* K) (σ : R →+* R)
    (hσι : ∀ x, σ (ι x) = ι (c x)) (hc : ∀ x, c (c x) = x) (hσ : ∀ x, σ (σ x) = x) {n : ℕ}
    (G : Matrix (Fin n) (Fin n) K) (hG : (G.map c)ᵀ = G) (hdet : G.det ≠ 0) (h2 : (2 : K) ≠ 0)
    (O : Subring (Matrix (Fin n) (Fin n) R)) (hb : ∀ M, ∃ d : ℕ, 0 < d ∧ d • M ∈ O)
    (e : R) (he : e * e = e) (hσe : σ e = e) (he0 : e ≠ 0) (heO : ∀ X ∈ O, e • X ∈ O)
    (N : ℕ) (hN : 0 < N) (hnak : ∀ X ∈ O, ∃ W ∈ O, (1 + e • (N • X)) * W = 1)
    (hapx : ∀ (M : Matrix (Fin n) (Fin n) R) (D : ℕ), 0 < D → ∃ M₀ : Matrix (Fin n) (Fin n) K, ∃ X ∈ O,
      (M - (G.map ι * M.map σ * (G.map ι)⁻¹)ᵀ) -
        (M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ) = D • X)
    (g h : Matrix (Fin n) (Fin n) R) (hg : h * g = 1) (hh : hᵀ * G.map ι * h.map σ = G.map ι)
    (lam : K) (hlam : lam * c lam = 1)
    (hu : IsUnit (1 + ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R))).det)
    (D : ℕ) (hD : 0 < D) :
    ∃ γ : Matrix (Fin n) (Fin n) K, γᵀ * G * γ.map c = G ∧
      ∃ X ∈ O, e • (γ.map ι * g - 1) = D • X := by
  have hmm : ∀ A : Matrix (Fin n) (Fin n) K, (A.map ι).map σ = (A.map c).map ι := by
    intro A
    ext i j
    simp [hσι]
  have cay : ∀ A B : Matrix (Fin n) (Fin n) R, (1 + A) * B = 1 → (1 - A) * B = (2 : R) • B - 1 := by
    intro A B hAB
    rw [add_mul, one_mul] at hAB
    rw [sub_mul, one_mul, two_smul, ← hAB]
    abel
  have hdu : IsUnit G.det := hdet.isUnit
  have hG' : ((G.map ι).map σ)ᵀ = G.map ι := by
    rw [hmm, ← Matrix.transpose_map, hG]
  have hdet' : IsUnit (G.map ι).det := by
    have := hdu.map ι
    rwa [RingHom.map_det] at this
  have h2' : IsUnit (2 : R) := by
    have := h2.isUnit.map ι
    rwa [map_ofNat] at this
  obtain ⟨cR1, cR2, -, -⟩ := GlobalTheory.T.cayleyTransform_unitary_skew_involutive R σ n (G.map ι) hσ hG' hdet' h2'
  obtain ⟨-, -, cK3, cK4⟩ := GlobalTheory.T.cayleyTransform_unitary_skew_involutive K c n G hc hG hdu h2.isUnit
  have hl : ι lam * σ (ι lam) = 1 := by rw [hσι, ← map_mul, hlam, map_one]
  set k : Matrix (Fin n) (Fin n) R := ι lam • (e • h + (1 - e) • (1 : Matrix (Fin n) (Fin n) R)) with hk
  have hku : kᵀ * G.map ι * k.map σ = G.map ι := preserves_form_smul_idempotent_glue σ _ h e _ he hσe hl hh
  obtain ⟨hS, hSu⟩ := cR1 k hku hu
  have hkS := cR2 k hu
  set S : Matrix (Fin n) (Fin n) R := (1 - k) * (1 + k)⁻¹ with hSdef
  set U : Matrix (Fin n) (Fin n) R := (1 + S)⁻¹ with hUdef
  have hU : U * (1 + S) = 1 := Matrix.nonsing_inv_mul _ hSu
  have hU' : (1 + S) * U = 1 := Matrix.mul_nonsing_inv _ hSu
  obtain ⟨d1, hd1, hO1⟩ := hb U
  obtain ⟨d2, hd2, hO2⟩ := hb ((2 * σ (ι lam)) • U)
  obtain ⟨d3, hd3, hO3⟩ := hb (U * g)
  obtain ⟨M₀, X, hX, hδ⟩ := hapx (ι 2⁻¹ • S) (N * d1 * d2 * d3 * D) (by positivity)
  have hu2 : ι 2⁻¹ + ι 2⁻¹ = 1 := by
    rw [← map_add, ← two_mul, mul_inv_cancel₀ h2, map_one]
  have hSS : ι 2⁻¹ • S - (G.map ι * (ι 2⁻¹ • S).map σ * (G.map ι)⁻¹)ᵀ = S := by
    have e1 : G.map ι * S.map σ = -(Sᵀ * G.map ι) := eq_neg_of_add_eq_zero_right hS
    rw [map_smul'', hσι, map_inv₀ c, map_ofNat c, mul_smul_comm, e1, smul_mul_assoc, neg_mul, mul_assoc,
      Matrix.mul_nonsing_inv _ hdet', mul_one, Matrix.transpose_smul, Matrix.transpose_neg,
      Matrix.transpose_transpose, smul_neg, sub_neg_eq_add, ← add_smul, hu2, one_smul]
  set S₀ : Matrix (Fin n) (Fin n) K := M₀ - (G * M₀.map c * G⁻¹)ᵀ with hS₀
  have hS₀s := cK4 M₀
  rw [← hS₀] at hS₀s
  have hT : M₀.map ι - (G.map ι * (M₀.map ι).map σ * (G.map ι)⁻¹)ᵀ = S₀.map ι := by
    rw [hS₀, Matrix.map_sub _ (map_sub ι), Matrix.transpose_map, Matrix.map_mul, Matrix.map_mul, hmm,
      map_inv' ι G hdu]
  rw [hSS, hT] at hδ
  set T : Matrix (Fin n) (Fin n) R := S₀.map ι with hTdef
  have hY : -(((d2 * d3 * D) • X) * (d1 • U)) ∈ O := neg_mem (mul_mem (nsmul_mem hX _) hO1)
  obtain ⟨W, hWO, hW'⟩ := hnak _ hY
  have hNY : N • (-(((d2 * d3 * D) • X) * (d1 • U))) = -((S - T) * U) := by
    rw [hδ, smul_neg]
    simp only [smul_mul_assoc, mul_smul_comm, smul_smul]
    congr 2
    ring
  rw [hNY] at hW'
  have hW : W * (1 + e • (-((S - T) * U))) = 1 := mul_eq_one_comm.1 hW'
  have h1T : (1 + S₀).map ι = 1 + T := by
    rw [Matrix.map_add _ (map_add ι), Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hS₀u : IsUnit (1 + S₀).det := by
    refine Ne.isUnit fun h0 => he0 ?_
    have e1 := congrArg Matrix.det (idem_factor e he S T U hU)
    have e2 : (1 + T).det = 0 := by
      rw [← h1T]
      have := RingHom.map_det ι (1 + S₀)
      rw [h0, map_zero] at this
      exact this.symm
    have e3 : IsUnit ((1 + e • (-((S - T) * U))) * (1 + S)).det := by
      rw [Matrix.det_mul]
      exact (Matrix.isUnit_det_of_left_inverse hW).mul hSu
    rw [Matrix.det_smul, Matrix.det_smul, e2, mul_zero] at e1
    have e4 := e3.mul_left_eq_zero.1 e1.symm
    have e5 := IsIdempotentElem.pow_succ_eq (Fintype.card (Fin n)) (show IsIdempotentElem e from he)
    rw [← e5, pow_succ, e4, zero_mul]
  set V : Matrix (Fin n) (Fin n) R := (1 + S₀)⁻¹.map ι with hVdef
  have hV : V * (1 + T) = 1 := by
    rw [← h1T, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ hS₀u,
      Matrix.map_one _ (map_zero ι) (map_one ι)]
  have hV' : (1 + T) * V = 1 := mul_eq_one_comm.1 hV
  have hγ := cK3 S₀ hS₀s hS₀u
  refine ⟨c lam • ((1 - S₀) * (1 + S₀)⁻¹), ?_, ?_⟩
  · rw [map_smul'', hc, Matrix.transpose_smul, smul_mul_assoc, smul_mul_assoc, mul_smul_comm, smul_smul,
      mul_comm, hlam, one_smul, hγ]
  · refine ⟨(N * d1) • (e • ((d2 • ((2 * σ (ι lam)) • U)) * W * X * (d3 • (U * g)))),
      nsmul_mem (heO _ (mul_mem (mul_mem (mul_mem hO2 hWO) hX) hO3)) _, ?_⟩
    have e1 : (c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι = σ (ι lam) • ((2 : R) • V - 1) := by
      rw [map_smul'', hσι, Matrix.map_mul, Matrix.map_sub _ (map_sub ι),
        Matrix.map_one _ (map_zero ι) (map_one ι), ← hVdef, ← hTdef, cay _ _ hV']
    have e2 : k = (2 : R) • U - 1 := by
      rw [← hkS, cay _ _ hU']
    have e3 : e • (1 : Matrix (Fin n) (Fin n) R) = e • (σ (ι lam) • (k * g)) := by
      rw [hk, smul_mul_assoc, smul_smul (σ _), mul_comm, hl, one_smul, ← smul_mul_assoc, smul_add,
        smul_smul, smul_smul, he, mul_sub, he, mul_one, sub_self, zero_smul, add_zero,
        smul_mul_assoc, hg]
    have e4 := idem_diff e he S T U V W hU hU' hV hV' hW
    have e5 : e • ((c lam • ((1 - S₀) * (1 + S₀)⁻¹)).map ι * g - 1) =
        (2 * σ (ι lam)) • ((e • (V - U)) * g) := by
      rw [smul_sub, e3, e1, e2]
      simp only [smul_mul_assoc, sub_mul, one_mul]
      module
    rw [e5, e4, hδ]
    simp only [smul_mul_assoc, mul_smul_comm, mul_assoc]
    module
end GlobalTheory.UnRep.WeakApprox
