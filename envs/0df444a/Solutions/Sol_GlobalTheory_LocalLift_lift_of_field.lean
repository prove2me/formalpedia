-- Prove2me | solution 1 for GlobalTheory.LocalLift.lift_of_field
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:08:41.637114+00:00
-- url     : https://prove2.me/submissions/96b78bbf-e865-42fd-a9ed-97f2f601911b

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleLagrangianTransverseFieldStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsAdmissibleIsUnitDetLocalInvolution
import Theorems.Thm_GlobalTheory_LocalLift_resInv_residue

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.LocalLift
namespace GlobalTheory.LocalLift
theorem _root_.solution
    (hF : ∀ {k : Type} [Field k] (c : k →+* k), (∀ x, c (c x) = x) → (2 : k) ≠ 0 →
      ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) k), IsUnit S.det → Sᵀ = -S.map c →
      ∀ (A C : Matrix (Fin n) (Fin n) k), (∀ u : Fin n → k, A *ᵥ u = 0 → C *ᵥ u = 0 → u = 0) →
        Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 →
        ∃ X : Matrix (Fin n) (Fin n) k, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det) :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] (c : O →+* O), (∀ x, c (c x) = x) → IsUnit (2 : O) →
    ∀ {n : ℕ} (S : Matrix (Fin n) (Fin n) O), IsUnit S.det → Sᵀ = -S.map c →
    ∀ (A B C D : Matrix (Fin n) (Fin n) O), IsUnit (Matrix.fromBlocks A B C D).det →
      (Matrix.fromBlocks A B C D)ᵀ * Matrix.fromBlocks 0 S S 0 * (Matrix.fromBlocks A B C D).map c =
        Matrix.fromBlocks 0 S S 0 →
      ∃ X : Matrix (Fin n) (Fin n) O, Xᵀ * S + S * X.map c = 0 ∧ IsUnit (A + X * C).det := by
  intro O _ _ c hc h2 n S hS hSc A B C D hdet hU
  set π := IsLocalRing.residue O with hπ
  set cb := resInv c hc with hcbdef
  have hcb : ∀ x, cb (π x) = π (c x) := resInv_residue c hc
  have hcbM : ∀ M : Matrix (Fin n) (Fin n) O, (M.map c).map π = (M.map π).map cb := by
    intro M; ext i j; simp [hcb]
  have hcbb : ∀ x, cb (cb x) = x := by
    intro x; obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    show cb (cb (π y)) = π y
    rw [hcb, hcb, hc]
  have h2k : (2 : IsLocalRing.ResidueField O) ≠ 0 := by
    have := (h2.map π).ne_zero; rwa [map_ofNat] at this
  have hSk : IsUnit (S.map π).det := by
    have := hS.map π; rwa [RingHom.map_det] at this
  have hSck : (S.map π)ᵀ = -(S.map π).map cb := by
    rw [← hcbM, ← Matrix.transpose_map, hSc]; ext i j; simp
  have h11 : Aᵀ * S * C.map c + Cᵀ * S * A.map c = 0 := by
    rw [fromBlocks_transpose, fromBlocks_map, fromBlocks_multiply, fromBlocks_multiply] at hU
    have := (Matrix.fromBlocks_inj.1 hU).1
    simp only [Matrix.mul_zero, Matrix.zero_mul, zero_add, add_zero] at this
    rw [add_comm]; simpa [Matrix.mul_assoc] using this
  have hinj : ∀ u, (A.map π) *ᵥ u = 0 → (C.map π) *ᵥ u = 0 → u = 0 := by
    intro u hA hC
    have hd : ((fromBlocks A B C D).map π).det ≠ 0 := by
      have := (hdet.map π).ne_zero; rwa [RingHom.map_det] at this
    have := Matrix.eq_zero_of_mulVec_eq_zero hd (v := Sum.elim u 0) (by
      rw [fromBlocks_map, fromBlocks_mulVec]; ext (i | i) <;> simp [hA, hC])
    funext i; simpa using congrFun this (Sum.inl i)
  have hiso : (A.map π)ᵀ * S.map π * (C.map π).map cb + (C.map π)ᵀ * S.map π * (A.map π).map cb = 0 := by
    have : (Aᵀ * S * C.map c + Cᵀ * S * A.map c).map π = 0 := by rw [h11]; ext; simp
    rw [Matrix.map_add _ (map_add π), Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul,
      Matrix.transpose_map, Matrix.transpose_map, hcbM, hcbM] at this
    exact this
  obtain ⟨Xb, hXadm, hXunit⟩ := hF cb hcbb h2k (S.map π) hSk hSck (A.map π) (C.map π) hinj hiso

  obtain ⟨X0, hX0⟩ : ∃ X0 : Matrix (Fin n) (Fin n) O, X0.map π = Xb :=
    ⟨Xb.map (fun x => (IsLocalRing.residue_surjective x).choose), by
      ext i j; exact (IsLocalRing.residue_surjective (Xb i j)).choose_spec⟩
  obtain ⟨h, hh⟩ := h2.exists_right_inv
  have hch : c h = h := by
    have h' : c 2 * c h = 1 := by rw [← map_mul, hh, map_one]
    rw [map_ofNat] at h'
    calc c h = (h * 2) * c h := by rw [mul_comm h 2, hh, one_mul]
      _ = h * (2 * c h) := by ring
      _ = h := by rw [h', mul_one]
  set Z0 := X0ᵀ * S with hZ0
  set Z := h • (Z0 + (Z0.map c)ᵀ) with hZ
  have hZh : (Z.map c)ᵀ = Z := by
    ext i j; simp only [hZ, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply,
      Matrix.add_apply, smul_eq_mul, map_mul, map_add, hch, hc]; ring
  set X := (Z * S⁻¹)ᵀ with hX
  have hSt : (S.map c)ᵀ = -S := by
    have : S.map c = -Sᵀ := by rw [hSc, neg_neg]
    rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
  have hSinv : S * (S⁻¹.map c)ᵀ = -1 := by
    have h1 : (S⁻¹.map c) * (S.map c) = 1 := by
      rw [← Matrix.map_mul, Matrix.nonsing_inv_mul S hS]; exact Matrix.map_one _ (map_zero c) (map_one c)
    have h2' := congrArg Matrix.transpose h1
    rw [Matrix.transpose_mul, Matrix.transpose_one, hSt, Matrix.neg_mul] at h2'
    rw [← neg_neg (S * _), h2']
  have hXS : Xᵀ * S = Z := by
    rw [hX, Matrix.transpose_transpose, Matrix.mul_assoc, Matrix.nonsing_inv_mul S hS, Matrix.mul_one]
  have hXc : X.map c = (S⁻¹.map c)ᵀ * Z := by
    rw [hX, Matrix.transpose_map, Matrix.map_mul, Matrix.transpose_mul, hZh]
  refine ⟨X, ?_, ?_⟩
  · rw [hXS, hXc, ← Matrix.mul_assoc, hSinv, Matrix.neg_mul, Matrix.one_mul, add_neg_cancel]
  · have hSbt : ((S.map π).map cb)ᵀ = -S.map π := by
      have : (S.map π).map cb = -(S.map π)ᵀ := by rw [hSck, neg_neg]
      rw [this, Matrix.transpose_neg, Matrix.transpose_transpose]
    have hZb : ((Xbᵀ * S.map π).map cb)ᵀ = Xbᵀ * S.map π := by
      rw [Matrix.map_mul, Matrix.transpose_mul, hSbt, ← Matrix.transpose_map, Matrix.transpose_transpose,
        Matrix.neg_mul]
      exact (eq_neg_of_add_eq_zero_left hXadm).symm
    have hZ0b : Z0.map π = Xbᵀ * S.map π := by
      rw [hZ0, Matrix.map_mul, Matrix.transpose_map, hX0]
    have hZm : Z.map π = π h • (Z0.map π + ((Z0.map c).map π)ᵀ) := by
      ext i j
      simp only [hZ, Matrix.map_apply, Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply,
        smul_eq_mul, map_mul, map_add]
    have hZπ : Z.map π = Xbᵀ * S.map π := by
      have h2h : π h * 2 = 1 := by rw [← map_ofNat π 2, ← map_mul, mul_comm, hh, map_one]
      rw [hZm, hcbM, hZ0b, hZb, ← two_smul (IsLocalRing.ResidueField O) (Xbᵀ * S.map π), smul_smul, h2h,
        one_smul]
    have hXπ : X.map π = Xb := by
      have hmm : (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := by
        ext i j
        simp only [Matrix.mul_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, map_mul]
      have e : (X.map π)ᵀ * S.map π = Xbᵀ * S.map π := by
        calc (X.map π)ᵀ * S.map π = (Xᵀ * S).map π := hmm
          _ = Z.map π := by rw [hXS]
          _ = Xbᵀ * S.map π := hZπ
      have e' := congrArg (· * (S.map π)⁻¹) e
      simp only [Matrix.mul_nonsing_inv_cancel_right _ _ hSk] at e'
      exact Matrix.transpose_inj.1 e'
    apply isUnit_of_map_unit π
    rw [RingHom.map_det, RingHom.mapMatrix_apply, Matrix.map_add _ (map_add π), Matrix.map_mul, hXπ]
    exact hXunit
end GlobalTheory.LocalLift
