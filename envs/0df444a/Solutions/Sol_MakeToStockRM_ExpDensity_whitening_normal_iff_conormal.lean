-- Prove2me | solution 1 for MakeToStockRM.ExpDensity.whitening_normal_iff_conormal
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:37:16.946727+00:00
-- url     : https://prove2.me/submissions/cfadc9a5-59fd-42c7-a7d8-9af34b44f9a2

import Mathlib
import Definitions.Def_MakeToStockRM_ExpDensity_covMatrix

namespace MakeToStockRM.ExpDensity

open Matrix

lemma aux_wnic_perp (n u : Fin 2 → ℝ) (hn : n ≠ 0) :
    (∀ w : Fin 2 → ℝ, n ⬝ᵥ w = 0 → u ⬝ᵥ w = 0) ↔ ∃ c : ℝ, u = c • n := by
  constructor
  · intro h
    have h1 := h ![-(n 1), n 0] (by simp [dotProduct, Fin.sum_univ_two]; ring)
    simp [dotProduct, Fin.sum_univ_two] at h1
    by_cases h0 : n 0 = 0
    · have h1' : n 1 ≠ 0 := by
        intro h1'; apply hn; ext i; fin_cases i <;> simp [h0, h1']
      refine ⟨u 1 / n 1, ?_⟩
      ext i; fin_cases i
      · simp [h0] at h1 ⊢
        rcases h1 with h1 | h1
        · exact h1
        · exact absurd h1 h1'
      · simp; field_simp
    · refine ⟨u 0 / n 0, ?_⟩
      ext i; fin_cases i
      · simp; field_simp
      · simp; field_simp; linarith
  · rintro ⟨c, rfl⟩ w hw
    rw [smul_dotProduct, hw, smul_zero]

end MakeToStockRM.ExpDensity

open MakeToStockRM.ExpDensity
open Matrix

theorem solution (σ δ ϱ : ℝ) (hσ : 0 < σ) (hδ : 0 < δ) (hϱ : |ϱ| < 1)
    (V : Matrix (Fin 2) (Fin 2) ℝ) (e : Fin 2 → ℝ)
    (hV : V * V.transpose = 1) (hVdet : V.det = 1) (he : ∀ i, 0 < e i)
    (hSigma : covMatrix σ δ ϱ = V.transpose * Matrix.diagonal e * V) :
    (∀ v w : Fin 2 → ℝ,
      ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
          ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w)
        = v ⬝ᵥ ((covMatrix σ δ ϱ)⁻¹ *ᵥ w)) ∧
    (∀ n v : Fin 2 → ℝ, n ≠ 0 →
      ((∀ w : Fin 2 → ℝ, n ⬝ᵥ w = 0 →
          ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ v)
            ⬝ᵥ ((Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V) *ᵥ w) = 0)
        ↔ ∃ c : ℝ, v = c • (covMatrix σ δ ϱ *ᵥ n))) := by
  set T := Matrix.diagonal (fun i => (Real.sqrt (e i))⁻¹) * V with hT
  set S := covMatrix σ δ ϱ with hS
  clear_value T S
  have hVV : V.transpose * V = 1 := mul_eq_one_comm.mp hV
  have hTT : T.transpose * T = V.transpose * Matrix.diagonal (fun i => (e i)⁻¹) * V := by
    rw [hT, Matrix.transpose_mul, Matrix.diagonal_transpose, Matrix.mul_assoc,
      ← Matrix.mul_assoc (Matrix.diagonal _), Matrix.diagonal_mul_diagonal, ← Matrix.mul_assoc]
    congr 3
    funext i
    rw [← mul_inv, Real.mul_self_sqrt (le_of_lt (he i))]
  have hSM : S * (T.transpose * T) = 1 := by
    rw [hSigma, hTT]
    calc V.transpose * Matrix.diagonal e * V * (V.transpose * Matrix.diagonal (fun i => (e i)⁻¹) * V)
        = V.transpose * Matrix.diagonal e * (V * V.transpose)
            * Matrix.diagonal (fun i => (e i)⁻¹) * V := by simp only [Matrix.mul_assoc]
      _ = V.transpose * (Matrix.diagonal e * Matrix.diagonal (fun i => (e i)⁻¹)) * V := by
            rw [hV, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = V.transpose * V := by
            rw [Matrix.diagonal_mul_diagonal]
            have : (fun i => e i * (e i)⁻¹) = (fun _ => (1:ℝ)) := by
              funext i; exact mul_inv_cancel₀ (ne_of_gt (he i))
            rw [this]
            change V.transpose * Matrix.diagonal (fun _ => (1:ℝ)) * V = _
            rw [show Matrix.diagonal (fun _ : Fin 2 => (1:ℝ)) = 1 from rfl, Matrix.mul_one]
      _ = 1 := hVV
  have hMS : (T.transpose * T) * S = 1 := mul_eq_one_comm.mp hSM
  have hinv : S⁻¹ = T.transpose * T := Matrix.inv_eq_right_inv hSM
  have key2 : ∀ v w, (T *ᵥ v) ⬝ᵥ (T *ᵥ w) = ((T.transpose * T) *ᵥ v) ⬝ᵥ w := by
    intro v w
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec]
  have key : ∀ v w, (T *ᵥ v) ⬝ᵥ (T *ᵥ w) = v ⬝ᵥ (S⁻¹ *ᵥ w) := by
    intro v w
    rw [key2, hinv, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.transpose_mul,
      Matrix.transpose_transpose]
  refine ⟨key, ?_⟩
  intro n v hn
  simp_rw [key2]
  rw [aux_wnic_perp n _ hn]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    calc v = (S * (T.transpose * T)) *ᵥ v := by rw [hSM, Matrix.one_mulVec]
      _ = S *ᵥ ((T.transpose * T) *ᵥ v) := by rw [Matrix.mulVec_mulVec]
      _ = c • (S *ᵥ n) := by rw [hc, Matrix.mulVec_smul]
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc, Matrix.mulVec_smul, Matrix.mulVec_mulVec, hMS, Matrix.one_mulVec]
