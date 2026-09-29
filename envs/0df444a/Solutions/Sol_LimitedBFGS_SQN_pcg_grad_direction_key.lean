-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_grad_direction_key
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T05:42:59.604999+00:00
-- url     : https://prove2.me/submissions/c2f9517e-b3fa-4953-bd04-21ef11f12aa0

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter

open Matrix
open LimitedBFGS.SQN


/-- The exact line search makes the new gradient orthogonal to the direction just
used, for every value of the step (this is `exactStep_minimizes_grad`, inlined so the
file needs no theorem import). -/
theorem grad_orth_step {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (x d : Fin n → ℝ) :
    grad A b (x + exactStep A b x d • d) ⬝ᵥ d = 0 := by
  have hA_tr : Aᵀ = A := (isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have haff (a : ℝ) : grad A b (x + a • d) = grad A b x + a • (A *ᵥ d) := by
    simp only [grad, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    abel
  have hs : (A *ᵥ d) ⬝ᵥ d = d ⬝ᵥ (A *ᵥ d) := by
    show (A *ᵥ d) ⬝ᵥ d = d ⬝ᵥ (A *ᵥ d)
    rw [dotProduct_comm]
  rw [haff (exactStep A b x d), add_dotProduct, smul_dotProduct, hs]
  simp only [exactStep, neg_dotProduct]
  by_cases hden : d ⬝ᵥ (A *ᵥ d) = 0
  · have hd0 : d = 0 := by
      by_contra hcon
      exact absurd hden (hA.dotProduct_mulVec_pos hcon).ne'
    simp [hd0]
  · rw [smul_eq_mul, div_mul_cancel₀ _ hden]
    ring

/-- Along the iteration, the direction at `k` is anti-parallel to the gradient in the
`H0` form: `g_k ⬝ᵥ d_k = -(H0 *ᵥ g_k) ⬝ᵥ g_k`. This is what rules out a vanishing
line-search step at a nonzero direction. -/
theorem pcg_grad_direction_key {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    let st := pcgIter A b H₀ x₀ k
    grad A b st.x ⬝ᵥ st.d = -((H₀ *ᵥ grad A b st.x) ⬝ᵥ grad A b st.x) := by
  classical
  cases k with
  | zero =>
      rw [show pcgIter A b H₀ x₀ 0 = ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩ by simp [pcgIter]]
      simp only [dotProduct_neg]
      congr 1
      exact dotProduct_comm _ _
  | succ j =>
      set stj := pcgIter A b H₀ x₀ j with hstj
      set gj := grad A b stj.x with hgj
      set dj := stj.d with hdj
      set aj := exactStep A b stj.x stj.d with haj
      set Adj := A *ᵥ stj.d with hadj
      have hgj1 : grad A b (stj.x + aj • stj.d) = gj + aj • Adj := by
        rw [hgj, hadj]
        simp only [grad, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
        abel
      have hsucc : pcgIter A b H₀ x₀ (j + 1)
          = ⟨stj.x + aj • stj.d,
            -(H₀ *ᵥ grad A b (stj.x + aj • stj.d))
              + (((grad A b (stj.x + aj • stj.d) - gj) ⬝ᵥ
                  (H₀ *ᵥ grad A b (stj.x + aj • stj.d)))
                / ((grad A b (stj.x + aj • stj.d) - gj) ⬝ᵥ stj.d)) • stj.d⟩ := by
        simp [pcgIter, hstj, haj, hdj, hadj]; rfl
      rw [hsucc]
      have hgj1d : grad A b (stj.x + aj • stj.d) ⬝ᵥ stj.d = 0 := by
        simpa using grad_orth_step A hA b stj.x stj.d
      simp only [dotProduct_add, dotProduct_neg]
      have h2 : grad A b (stj.x + aj • stj.d) ⬝ᵥ
          ((grad A b (stj.x + aj • stj.d) - gj) ⬝ᵥ
            (H₀ *ᵥ grad A b (stj.x + aj • stj.d))
            / (grad A b (stj.x + aj • stj.d) - gj) ⬝ᵥ stj.d)
          • stj.d = 0 := by
        rw [dotProduct_smul, hgj1d]
        ring
      rw [h2, add_zero]
      congr 1
      exact dotProduct_comm _ _

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (x₀ : Fin n → ℝ) (k : ℕ) :
    grad A b (pcgIter A b H₀ x₀ k).x ⬝ᵥ (pcgIter A b H₀ x₀ k).d
      = -((H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ k).x) ⬝ᵥ grad A b (pcgIter A b H₀ x₀ k).x) :=
  pcg_grad_direction_key A hA b H₀ x₀ k
