-- Prove2me | solution 1 for LinearOptimization.no_arbitrage_iff_state_prices
-- status  : ACCEPTED   (prove)
-- author  : @Harry_Xu
-- created : 2026-08-05T20:55:32.049934+00:00
-- url     : https://prove2.me/submissions/5027c5db-ace7-4473-be90-6f6bbfe0f4bb

import Theorems.Thm_LinearOptimization_farkas_cone_corollary

open Matrix

theorem solution {m n : ℕ} (R : Matrix (Fin m) (Fin n) ℝ)
    (p : Fin n → ℝ) :
    (∀ x : Fin n → ℝ, 0 ≤ R.mulVec x → 0 ≤ p ⬝ᵥ x) ↔
      ∃ q : Fin m → ℝ, 0 ≤ q ∧ ∀ i, p i = ∑ s, q s * R s i := by
  classical
  have hdual (q : Fin m → ℝ) (x : Fin n → ℝ) :
      q ⬝ᵥ R.mulVec x = Rᵀ.mulVec q ⬝ᵥ x := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    funext j
    simp [Matrix.vecMul, Matrix.mulVec, dotProduct, mul_comm]
  constructor
  · intro h
    let rows : Fin m → (Fin n → ℝ) := fun s i ↦ R s i
    have hsep (x : Fin n → ℝ) (hx : ∀ s, 0 ≤ x ⬝ᵥ rows s) :
        0 ≤ x ⬝ᵥ p := by
      have hrx : 0 ≤ R.mulVec x := by
        intro s
        simpa [rows, Matrix.mulVec, dotProduct, mul_comm] using hx s
      simpa [dotProduct, mul_comm] using h x hrx
    obtain ⟨q, hq, hp⟩ :=
      LinearOptimization.farkas_cone_corollary rows p hsep
    refine ⟨q, hq, ?_⟩
    intro i
    have hi := congrFun hp i
    simpa [rows, mul_comm] using hi
  · rintro ⟨q, hq, hp⟩ x hx
    have hAT : Rᵀ.mulVec q = p := by
      funext i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using (hp i).symm
    have hnonneg : 0 ≤ q ⬝ᵥ R.mulVec x := by
      exact Finset.sum_nonneg fun s hs ↦ mul_nonneg (hq s) (hx s)
    rw [hdual, hAT] at hnonneg
    exact hnonneg
