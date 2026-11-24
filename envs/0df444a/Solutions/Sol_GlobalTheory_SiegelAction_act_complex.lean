-- Prove2me | solution 1 for GlobalTheory.SiegelAction.act_complex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:02:40.535803+00:00
-- url     : https://prove2.me/submissions/2ec79926-8a0e-4240-a8f7-b3d276d6c743

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_SpanningFamilies_IMemSiegel
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_SiegelThetaTransformation_SymplecticSiegelActionMemUpperHalfSpaceAndCocycl
import Theorems.Thm_GlobalTheory_SiegelAction_posDef_ofReal
import Theorems.Thm_GlobalTheory_SiegelAction_posDef_of_ofReal
import Theorems.Thm_GlobalTheory_SiegelAction_sub_conj_eq
import Theorems.Thm_GlobalTheory_SiegelAction_block_identity

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex GlobalTheory.SW
open scoped ComplexConjugate Real
open GlobalTheory GlobalTheory.SiegelAction
open scoped ComplexOrder
variable {ι : Type} [Fintype ι] [DecidableEq ι]
namespace GlobalTheory.SiegelAction
theorem _root_.solution {A B C D τ : Matrix ι ι ℂ}
    (h : fromBlocks A B C D ∈ symplecticGroup ι ℂ) (hA : A.map conj = A) (hB : B.map conj = B)
    (hC : C.map conj = C) (hD : D.map conj = D) (hτ : τ ∈ Siegel ι) :
    (C * τ + D).det ≠ 0 ∧ (A * τ + B) * (C * τ + D)⁻¹ ∈ Siegel ι ∧ ((C * τ + D)⁻¹ * C).IsSymm ∧
      (C * τ + D)ᵀ * ((A * τ + B) * (C * τ + D)⁻¹).map (fun z => (z.im : ℂ)) *
        (C * τ + D).map conj = τ.map (fun z => (z.im : ℂ)) := by
  obtain ⟨hs, hp⟩ := hτ
  have hY : (τ.map (fun z => (z.im : ℂ))).PosDef := posDef_ofReal hp
  have e1 := block_identity (τ' := τ) h hs
  have e2 := block_identity (τ' := τ.map conj) h hs
  have cP : (A * τ + B).map conj = A * τ.map conj + B := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hA, hB]
  have cQ : (C * τ + D).map conj = C * τ.map conj + D := by
    rw [Matrix.map_add _ (map_add conj), Matrix.map_mul, hC, hD]
  have e3 : C * (C * τ + D)ᵀ = (C * τ + D) * Cᵀ := by
    have ht := SymplecticGroup.transpose_mem h
    rw [fromBlocks_transpose] at ht
    obtain ⟨-, h2, -⟩ := SymplecticGroup.fromBlocks_mem_iff.1 ht
    simp only [transpose_transpose] at h2
    simp only [transpose_add, transpose_mul, hs.eq, Matrix.mul_add, Matrix.add_mul, h2,
      Matrix.mul_assoc]
  rw [← cP, ← cQ, sub_conj_eq] at e2
  rw [sub_self, sub_eq_zero] at e1
  generalize A * τ + B = P at *
  generalize C * τ + D = Q at *
  have h2I : (2 * I : ℂ) ≠ 0 := by simp
  have hQt : (Q.map conj)ᴴ = Qᵀ := by
    ext i j; simp
  have hdet : Q.det ≠ 0 := by
    intro h0
    have h0' : (Q.map conj).det = 0 := by
      have := RingHom.map_det (starRingEnd ℂ) Q
      rw [h0, map_zero] at this
      exact this.symm
    obtain ⟨v, hv, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0'
    have hQv' : star v ᵥ* Qᵀ = 0 := by
      rw [← hQt, ← star_mulVec, hQv, star_zero]
    have hpos := hY.dotProduct_mulVec_pos hv
    have := congrArg (fun M => star v ⬝ᵥ M *ᵥ v) e2
    simp only [sub_mulVec, ← mulVec_mulVec, hQv, mulVec_zero, dotProduct_sub, dotProduct_zero,
      smul_mulVec, dotProduct_smul, smul_eq_mul] at this
    rw [dotProduct_mulVec (star v) Qᵀ, hQv', zero_dotProduct, sub_zero] at this
    exact hpos.ne' ((mul_eq_zero.1 this.symm).resolve_left h2I)
  have hu : IsUnit Q.det := hdet.isUnit
  have hut : IsUnit Qᵀ.det := by rwa [det_transpose]
  have hWQ : P * Q⁻¹ * Q = P := nonsing_inv_mul_cancel_right _ _ hu
  have hQW : Qᵀ * (P * Q⁻¹) = Pᵀ := by
    rw [← Matrix.mul_assoc, ← e1, mul_nonsing_inv_cancel_right _ _ hu]
  have hWs : (P * Q⁻¹).IsSymm := by
    rw [IsSymm, transpose_mul, transpose_nonsing_inv, ← hQW, nonsing_inv_mul_cancel_left _ _ hut]
  have hcW : (P * Q⁻¹).map conj * Q.map conj = P.map conj := by
    rw [← Matrix.map_mul, hWQ]
  have key : Qᵀ * (P * Q⁻¹).map (fun z => (z.im : ℂ)) * Q.map conj =
      τ.map (fun z => (z.im : ℂ)) := by
    apply smul_right_injective _ h2I
    simp only
    rw [← e2, ← Matrix.smul_mul, ← Matrix.mul_smul, ← sub_conj_eq, Matrix.mul_sub, Matrix.sub_mul,
      hQW, Matrix.mul_assoc Qᵀ, hcW]
  refine ⟨hdet, ⟨hWs, posDef_of_ofReal ?_⟩, ?_, key⟩
  · have huc : IsUnit (Q.map conj) := by
      rw [isUnit_iff_isUnit_det]
      have := RingHom.map_det (starRingEnd ℂ) Q
      exact this ▸ hu.map (starRingEnd ℂ)
    refine (Matrix.IsUnit.posDef_star_left_conjugate_iff huc).1 ?_
    rw [star_eq_conjTranspose, hQt]
    rw [← key] at hY
    exact hY
  · rw [IsSymm, transpose_mul, transpose_nonsing_inv]
    calc Cᵀ * Qᵀ⁻¹ = Q⁻¹ * (Q * Cᵀ) * Qᵀ⁻¹ := by rw [nonsing_inv_mul_cancel_left _ _ hu]
      _ = Q⁻¹ * C := by
        rw [← e3, Matrix.mul_assoc, mul_nonsing_inv_cancel_right _ _ hut]
end GlobalTheory.SiegelAction
