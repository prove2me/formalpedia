-- Prove2me | solution 1 for GlobalTheory.exists_unimodular_posDef_adjoint_action
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T23:51:38.062046+00:00
-- url     : https://prove2.me/submissions/1bb36f9c-ee95-4b92-bff5-d1723e0581c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsIntMatrixTransposeMulEqSmulOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnimodularPosDefAdjointAction
import Theorems.Thm_GlobalTheory_zarhinBlock_real_posDef_det
import Theorems.Thm_GlobalTheory_zarhinAction_adjoint
import Theorems.Thm_GlobalTheory_mul_adjugate_eq_adjugate_mul_of_adjoint
import Theorems.Thm_GlobalTheory_exists_int_matrix_transpose_mul_eq_smul_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Kronecker
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution (R : Type) [CommRing R] (σ : R →+* R)
    (hσ : ∀ a, σ (σ a) = a) (m : ℕ) (B0 : Matrix (Fin m) (Fin m) ℤ)
    (ρ0 : R →+* Matrix (Fin m) (Fin m) ℤ) (hm : 1 ≤ m) (hs : B0.transpose = B0)
    (hp : (B0.map (Int.cast : ℤ → ℝ)).PosDef)
    (hadj : ∀ a, (ρ0 a).transpose * B0 = B0 * ρ0 (σ a)) :
    ∃ (r : ℕ) (b : Matrix (Fin r) (Fin r) ℤ) (ρ : R →+* Matrix (Fin r) (Fin r) ℤ),
      1 ≤ r ∧ b.transpose = b ∧ (b.map (Int.cast : ℤ → ℝ)).PosDef ∧ IsUnit b.det ∧
        ∀ a, (ρ a).transpose * b = b * ρ (σ a) := by
  have hcast : ∀ {k : Type} [Fintype k] [DecidableEq k] (M : Matrix k k ℤ),
      (M.map (Int.cast : ℤ → ℝ)).det = (M.det : ℝ) := fun M => by
    simpa using ((Int.castRingHom ℝ).map_det M).symm
  have hDR : (0 : ℝ) < (B0.det : ℝ) := hcast B0 ▸ hp.det_pos
  have hD : 0 < B0.det := by exact_mod_cast hDR
  obtain ⟨s, hsD⟩ : ∃ s : ℕ, B0.det = 1 + s := ⟨(B0.det - 1).toNat, by omega⟩
  obtain ⟨x, hx, -⟩ := exists_int_matrix_transpose_mul_eq_smul_one s
  set b := fromBlocks (B0.adjugate ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ))
    ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ xᵀ) ((1 : Matrix (Fin m) (Fin m) ℤ) ⊗ₖ x)
    (B0 ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℤ)) with hb
  have hsym : bᵀ = b := by
    simp only [hb, fromBlocks_transpose, ← kroneckerMap_transpose, transpose_transpose,
      transpose_one, adjugate_transpose, hs]
  have hk : ∀ (M : Matrix (Fin m) (Fin m) ℤ) (N : Matrix (Fin 4) (Fin 4) ℤ),
      (M ⊗ₖ N).map (Int.cast : ℤ → ℝ) = M.map (Int.cast : ℤ → ℝ) ⊗ₖ N.map (Int.cast : ℤ → ℝ) := by
    intro M N
    ext i j
    simp [kroneckerMap_apply]
  have hxR : (x.map (Int.cast : ℤ → ℝ))ᵀ * x.map (Int.cast : ℤ → ℝ) = (s : ℝ) • 1 := by
    have := congrArg (fun M => (Int.castRingHom ℝ).mapMatrix M) hx
    simp only [map_mul, map_zsmul, map_one] at this
    rw [← Int.cast_smul_eq_zsmul ℝ] at this
    simpa [transpose_map] using this
  have hAR : (B0.adjugate).map (Int.cast : ℤ → ℝ) =
      (1 + (s : ℝ)) • (B0.map (Int.cast : ℤ → ℝ))⁻¹ := by
    have h1 : (B0.adjugate).map (Int.cast : ℤ → ℝ) = (B0.map (Int.cast : ℤ → ℝ)).adjugate := by
      simpa using (Int.castRingHom ℝ).map_adjugate B0
    have h2 : (1 + (s : ℝ)) = (B0.det : ℝ) := by rw [hsD]; push_cast; rfl
    rw [h1, h2, Matrix.inv_def, hcast, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hDR.ne',
      one_smul]
  have hreal := zarhinBlock_real_posDef_det _ _ _ _ hp hAR hxR
  have hbR : b.map (Int.cast : ℤ → ℝ) =
      fromBlocks (B0.adjugate.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ))
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ (x.map (Int.cast : ℤ → ℝ))ᵀ)
        ((1 : Matrix (Fin m) (Fin m) ℝ) ⊗ₖ x.map (Int.cast : ℤ → ℝ))
        (B0.map (Int.cast : ℤ → ℝ) ⊗ₖ (1 : Matrix (Fin 4) (Fin 4) ℝ)) := by
    rw [hb, fromBlocks_map, hk, hk, hk, hk, Matrix.map_one _ Int.cast_zero Int.cast_one,
      Matrix.map_one _ Int.cast_zero Int.cast_one, transpose_map]
  rw [← hbR, hcast] at hreal
  have hdet : b.det = 1 := by exact_mod_cast hreal.2
  have hact := zarhinAction_adjoint σ hσ ρ0 B0 B0.adjugate x hadj
    (fun a => mul_adjugate_eq_adjugate_mul_of_adjoint _ _ _ hD.ne' (hadj a))
  rw [← hb] at hact
  let e := Fintype.equivFin ((Fin m × Fin 4) ⊕ (Fin m × Fin 4))
  refine ⟨_, reindex e e b, ((reindexAlgEquiv ℤ ℤ e).toRingEquiv.toRingHom).comp
    (zarhinAction σ ρ0), ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]; omega
  · rw [transpose_reindex, hsym]
  · exact hreal.1.submatrix e.symm.injective
  · rw [det_reindex_self, hdet]; exact isUnit_one
  · intro a
    change (reindex e e (zarhinAction σ ρ0 a))ᵀ * _ = _ * reindex e e (zarhinAction σ ρ0 (σ a))
    simp only [reindex_apply, transpose_submatrix, submatrix_mul_equiv, hact]
end GlobalTheory
