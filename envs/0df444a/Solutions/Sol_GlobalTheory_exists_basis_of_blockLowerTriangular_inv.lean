-- Prove2me | solution 1 for GlobalTheory.exists_basis_of_blockLowerTriangular_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:39:02.761558+00:00
-- url     : https://prove2.me/submissions/e52f6564-959e-48f8-8ac2-8a7e347441c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsBasisOfBlockLowerTriangularInv

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix
namespace GlobalTheory
theorem _root_.solution (O M : Type) [CommRing O] [AddCommGroup M] [Module O M]
    (d k k' : ℕ) (lbs : Module.Basis (Fin k') O M)
    (P : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k') O) (P' : Matrix (Fin d ⊕ Fin k') (Fin d ⊕ Fin k) O)
    (h1 : P * P' = 1) (h2 : P' * P = 1) (hz : ∀ i j, P (Sum.inl i) (Sum.inr j) = 0) :
    ∃ lb : Module.Basis (Fin k) O M, ∀ j, lb j = ∑ j', P (Sum.inr j) (Sum.inr j') • lbs j' := by
  have hAA : P.toBlocks₁₁ * P'.toBlocks₁₁ = 1 := by
    ext i i'
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inl i')
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁] using this
  have hA'A : P'.toBlocks₁₁ * P.toBlocks₁₁ = 1 := mul_eq_one_comm.mp hAA
  have hAB : P.toBlocks₁₁ * P'.toBlocks₁₂ = 0 := by
    ext i j
    have := congrFun (congrFun h1 (Sum.inl i)) (Sum.inr j)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂] using this
  have hB : P'.toBlocks₁₂ = 0 := by
    calc P'.toBlocks₁₂ = (P'.toBlocks₁₁ * P.toBlocks₁₁) * P'.toBlocks₁₂ := by rw [hA'A, Matrix.one_mul]
      _ = P'.toBlocks₁₁ * (P.toBlocks₁₁ * P'.toBlocks₁₂) := Matrix.mul_assoc _ _ _
      _ = 0 := by rw [hAB, Matrix.mul_zero]
  have hb : ∀ a j, P' (Sum.inl a) (Sum.inr j) = 0 := fun a j => by
    simpa [Matrix.toBlocks₁₂] using congrFun (congrFun hB a) j
  have hDD : P.toBlocks₂₂ * P'.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h1 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hb, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  have hD'D : P'.toBlocks₂₂ * P.toBlocks₂₂ = 1 := by
    ext j j2
    have := congrFun (congrFun h2 (Sum.inr j)) (Sum.inr j2)
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, hz, Matrix.one_apply, Matrix.toBlocks₂₂] using this
  set D := P.toBlocks₂₂ with hDdef
  set D' := P'.toBlocks₂₂
  let L : (Fin k → O) ≃ₗ[O] (Fin k' → O) :=
    LinearEquiv.ofLinear (Matrix.toLin' Dᵀ) (Matrix.toLin' D'ᵀ)
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hD'D, Matrix.transpose_one, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, ← Matrix.transpose_mul, hDD, Matrix.transpose_one, Matrix.toLin'_one])
  refine ⟨Module.Basis.ofEquivFun (lbs.equivFun.trans L.symm), fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.symm_symm, Module.Basis.equivFun_symm_apply]
  refine Finset.sum_congr rfl fun j' _ => ?_
  congr 1
  simp [L, Matrix.mulVec, dotProduct, Pi.single_apply, hDdef, Matrix.toBlocks₂₂]
end GlobalTheory
