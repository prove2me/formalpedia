-- Prove2me | solution 1 for ModernConvex.Spectral.convex_symmetric_eig_eq_max_diag
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T16:30:03.207889+00:00
-- url     : https://prove2.me/submissions/424f53fc-8954-4ed1-afe5-1768d9ec005a

import Mathlib
import Definitions.Def_ModernConvex_Spectral_SDR

open Matrix
open ModernConvex.Spectral

lemma g71m_diag {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ((hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))ᵀ * (hA.eigenvectorUnitary : Matrix _ _ ℝ) = 1 ∧
    (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) * ((hA.eigenvectorUnitary : Matrix _ _ ℝ))ᵀ = 1 ∧
    ((hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))ᵀ * A * (hA.eigenvectorUnitary : Matrix _ _ ℝ)
      = diagonal hA.eigenvalues := by
  have hs : star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) =
      ((hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ))ᵀ := by
    rw [star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
  have h1 : star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = 1 := Unitary.coe_star_mul_self _
  have h2 : (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) *
      star (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) = 1 := Unitary.coe_mul_star_self _
  have h3 := hA.conjStarAlgAut_star_eigenvectorUnitary
  rw [Unitary.conjStarAlgAut_star_apply] at h3
  rw [hs] at h1 h2 h3
  refine ⟨h1, h2, ?_⟩
  rw [h3]
  congr 1

lemma g71m_eig_perm {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : A.IsHermitian) :
    ∃ σ : Equiv.Perm (Fin m), hA.eigenvalues = eigVec A ∘ σ := by
  refine ⟨(Fintype.equivOfCardEq (Fintype.card_fin _)).symm.trans
    (finCongr (Fintype.card_fin m)), ?_⟩
  funext i
  simp only [eigVec, dif_pos hA, Function.comp_apply, Equiv.trans_apply, finCongr_apply,
    Matrix.IsHermitian.eigenvalues]
  congr 1

theorem solution {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (hf : ConvexOn ℝ Set.univ f) (hsym : IsSymmetricFn f) (A : Matrix (Fin m) (Fin m) ℝ)
    (hA : A.IsHermitian) :
    IsGreatest {r : ℝ | ∃ V : Matrix (Fin m) (Fin m) ℝ, Vᵀ * V = 1 ∧ r = f (diag (Vᵀ * A * V))}
      (f (eigVec A)) := by
  obtain ⟨h1, h2, h3⟩ := g71m_diag A hA
  set U : Matrix (Fin m) (Fin m) ℝ := (hA.eigenvectorUnitary : Matrix (Fin m) (Fin m) ℝ) with hU
  obtain ⟨σ, hσ⟩ := g71m_eig_perm A hA
  have hfl : f hA.eigenvalues = f (eigVec A) := by rw [hσ, hsym]
  refine ⟨⟨U, h1, ?_⟩, ?_⟩
  · rw [h3, diag_diagonal, hfl]
  · rintro r ⟨V, hV, rfl⟩
    set W : Matrix (Fin m) (Fin m) ℝ := Uᵀ * V with hW
    have hWW : Wᵀ * W = 1 := by
      rw [hW, transpose_mul, transpose_transpose]
      calc Vᵀ * U * (Uᵀ * V) = Vᵀ * (U * Uᵀ) * V := by simp only [Matrix.mul_assoc]
        _ = 1 := by rw [h2, Matrix.mul_one, hV]
    have hWW' : W * Wᵀ = 1 := mul_eq_one_comm.mp hWW
    have hA' : A = U * diagonal hA.eigenvalues * Uᵀ := by
      rw [← h3]
      calc A = (U * Uᵀ) * A * (U * Uᵀ) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
        _ = U * (Uᵀ * A * U) * Uᵀ := by simp only [Matrix.mul_assoc]
    have hd : diag (Vᵀ * A * V) = fun i => ∑ j, (W j i) ^ 2 * hA.eigenvalues j := by
      have : Vᵀ * A * V = Wᵀ * diagonal hA.eigenvalues * W := by
        calc Vᵀ * A * V = Vᵀ * (U * diagonal hA.eigenvalues * Uᵀ) * V := by
              conv_lhs => rw [hA']
          _ = Wᵀ * diagonal hA.eigenvalues * W := by
              rw [hW, transpose_mul, transpose_transpose]
              simp only [Matrix.mul_assoc]
      rw [this]
      funext i
      simp only [diag_apply, mul_apply, diagonal_apply, transpose_apply, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    set P : Matrix (Fin m) (Fin m) ℝ := fun i j => (W j i) ^ 2 with hP
    have hPd : P ∈ doublyStochastic ℝ (Fin m) := by
      rw [mem_doublyStochastic_iff_sum]
      refine ⟨fun i j => sq_nonneg _, fun i => ?_, fun j => ?_⟩
      · have := congrFun (congrFun hWW i) i
        simpa [mul_apply, sq, P] using this
      · have := congrFun (congrFun hWW' j) j
        simpa [mul_apply, sq, P] using this
    obtain ⟨w, hw0, hw1, hwP⟩ := exists_eq_sum_perm_of_mem_doublyStochastic hPd
    have hPx : diag (Vᵀ * A * V) = ∑ τ, w τ • (hA.eigenvalues ∘ τ) := by
      have : diag (Vᵀ * A * V) = P *ᵥ hA.eigenvalues := by
        rw [hd]; funext i; simp [mulVec, dotProduct, P]
      rw [this, ← hwP, sum_mulVec]
      refine Finset.sum_congr rfl fun τ _ => ?_
      rw [smul_mulVec, Matrix.permMatrix_mulVec]
    rw [hPx, ← hfl]
    calc f (∑ τ, w τ • (hA.eigenvalues ∘ τ)) ≤ ∑ τ, w τ • f (hA.eigenvalues ∘ τ) :=
          hf.map_sum_le (fun τ _ => hw0 τ) hw1 (fun τ _ => Set.mem_univ _)
      _ = ∑ τ, w τ • f hA.eigenvalues := by
          refine Finset.sum_congr rfl fun τ _ => ?_
          rw [hsym]
      _ = f hA.eigenvalues := by rw [← Finset.sum_smul, hw1, one_smul]
