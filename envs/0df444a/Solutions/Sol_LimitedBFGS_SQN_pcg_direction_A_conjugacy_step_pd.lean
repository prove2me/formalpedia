-- Prove2me | solution 1 for LimitedBFGS.SQN.pcg_direction_A_conjugacy_step_pd
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T06:04:26.629976+00:00
-- url     : https://prove2.me/submissions/144689c9-d68c-4432-acbb-5bddef1624cb

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_direction_key

open Matrix
open LimitedBFGS.SQN

/-- The exact line search makes the new gradient orthogonal to the direction just used,
for every value of the step. This is `exactStep_minimizes_grad`, inlined so the file needs
no theorem import. -/
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

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (k : ℕ) :
    (pcgIter A b H₀ x₀ (k + 1)).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ k).d) = 0 := by
  classical
  set st := pcgIter A b H₀ x₀ k with hst
  set d := st.d with hd
  set Ad := A *ᵥ d with hAd
  set a := exactStep A b st.x st.d with ha
  set g := grad A b st.x with hg
  set g1 := grad A b (st.x + a • d) with hg1
  set Hg := H₀ *ᵥ g1 with hHg
  set y := g1 - g with hy
  -- `A` is positive definite, hence symmetric; this gives self-adjointness of
  -- the bilinear form `u ᵀ A v`, stated once and reused.
  have hA_tr : Aᵀ = A := (isHermitian_iff_isSymm.mp hA.isHermitian).eq
  have hsymm : ∀ u v : Fin n → ℝ, u ⬝ᵥ (A *ᵥ v) = v ⬝ᵥ (A *ᵥ u) := by
    intro u v
    have h := dotProduct_transpose_mulVec (A := A) (x := u) (y := v)
    rwa [hA_tr] at h
  -- Affineness of the gradient, in the general form used twice below.
  have haff (x : Fin n → ℝ) (a : ℝ) (q : Fin n → ℝ) :
      grad A b (x + a • q) = grad A b x + a • (A *ᵥ q) := by
    simp only [grad, Matrix.mulVec_add, Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul]
    abel
  have haff' : g1 = g + a • Ad := by rw [hg1, hg, ha, hd]; exact haff _ _ _
  have hyad : y = a • Ad := by rw [hy, haff']; abel
  -- `H0 *ᵥ u = 0` forces `u = 0`, by strict positivity of the `H0` form.
  have hH0_nil (u : Fin n → ℝ) (hu : H₀ *ᵥ u = 0) : u = 0 := by
    by_contra hcon
    have hpos : 0 < u ⬝ᵥ (H₀ *ᵥ u) := hH₀.dotProduct_mulVec_pos hcon
    rw [hu] at hpos
    exact absurd hpos (not_lt_of_ge (by simp))
  -- Self-adjointness of the form `u ᵀ A v`, at the pair actually needed.
  have hHgAd : Hg ⬝ᵥ Ad = Ad ⬝ᵥ Hg := by
    rw [hAd, dotProduct_comm (A *ᵥ d) Hg, hsymm Hg d]
  -- Unfold the successor state once, keeping the abbreviations intact.
  have hsucc : pcgIter A b H₀ x₀ (k + 1)
      = ⟨st.x + a • d, -Hg + ((y ⬝ᵥ Hg) / (y ⬝ᵥ d)) • d⟩ := by
    simp only [pcgIter, hst, ha, hd, hg1, hHg, hy]
    rfl
  rw [hsucc]
  simp only [neg_dotProduct, add_dotProduct]
  rw [hHgAd, hyad]
  -- Both summands now carry the common factor `a`.
  have hcomm : d ⬝ᵥ Ad = Ad ⬝ᵥ d := by
    show d ⬝ᵥ (A *ᵥ d) = (A *ᵥ d) ⬝ᵥ d
    rw [dotProduct_comm]
  by_cases hd0 : d = 0
  · -- With `d = 0` the direction is zero and every pairing in sight vanishes.
    simp [hd0, hAd]
  by_cases ha0 : a = 0
  · -- `a = 0` means the step does not move: `g1 = g`, `y = 0`, `beta = 0`, so the
    -- successor direction is `-H0 *ᵥ g`. The goal is then `(H0 *ᵥ g) ⬝ᵥ (A *ᵥ d) = 0`.
    -- From `a = 0` and `dᵀAd > 0` we get `g ⬝ᵥ d = 0`; combined with the direction
    -- recurrence `d = -H0 *ᵥ g + beta_{k-1} d_{k-1}` and `g ⬝ᵥ d_{k-1} = 0` this gives
    -- `gᵀ H0 g = 0`, so `H0 *ᵥ g = 0` and both factors vanish.
    -- `a = 0` and `dᵀAd > 0` force `g ⬝ᵥ d = 0`.
    have hgd : g ⬝ᵥ d = 0 := by
      -- With `a = 0` the step does not move, so the proved one-step conjugacy
      -- `exactStep_minimizes_grad` applies at the *same* point and gives this.
      have ha0' : exactStep A b st.x st.d = 0 := ha0 ▸ rfl
      have h0 : grad A b (st.x + exactStep A b st.x st.d • st.d) ⬝ᵥ st.d = 0 :=
        grad_orth_step A hA b st.x st.d
      rw [ha0', zero_smul, add_zero] at h0
      simpa [hg, hd] using h0
    -- `Hg = H0 *ᵥ g` because `a = 0` leaves the iterate, hence the gradient, fixed.
    have hHg_g : Hg = H₀ *ᵥ g := by
      have : grad A b (st.x + a • st.d) = grad A b st.x + a • A *ᵥ st.d := haff _ _ _
      rw [hHg, hg1, ha, this]
      rw [ha0, zero_smul, add_zero, hg]
    -- The direction at `k` is anti-parallel to the gradient in the `H0` form:
    -- `g ⬝ᵥ d = -((H0 *ᵥ g) ⬝ᵥ g)`. Since `g ⬝ᵥ d = 0`, the `H0`-pairing vanishes,
    -- and positive definiteness of `H0` then gives `Hg = 0`.
    have hHg_nil : Hg = 0 := by
      have hkey : g ⬝ᵥ d = -((H₀ *ᵥ g) ⬝ᵥ g) := by
        simpa [hg, hd, hst] using pcg_grad_direction_key A hA b H₀ x₀ k
      have hzero : -(H₀ *ᵥ g ⬝ᵥ g) = 0 := hkey.symm.trans (hgd ▸ rfl)
      have hself : (H₀ *ᵥ g) ⬝ᵥ g = 0 := neg_eq_zero.mp hzero
      rw [hHg_g]
      -- `H0` is positive definite, so `H0 *ᵥ g = 0` forces `g = 0`.
      have hgnil : H₀ *ᵥ g = 0 := by
        by_contra hcon
        have hne : g ≠ 0 := fun hz => hcon (by rw [hz, Matrix.mulVec_zero])
        have hpos2 : 0 < g ⬝ᵥ (H₀ *ᵥ g) := hH₀.dotProduct_mulVec_pos hne
        have hcomm : g ⬝ᵥ (H₀ *ᵥ g) = (H₀ *ᵥ g) ⬝ᵥ g := dotProduct_comm _ _
        rw [hcomm, hself] at hpos2
        exact absurd hpos2 (not_lt_of_ge (by simp))
      have hgzero : g = 0 := hH0_nil g hgnil
      rw [hgzero, Matrix.mulVec_zero]
    simp [hHg_nil]
  · -- `a ≠ 0` and `d ⬝ᵥ (A *ᵥ d) > 0` let the shared factor cancel inside the quotient.
    have hpos : 0 < d ⬝ᵥ (A *ᵥ d) := hA.dotProduct_mulVec_pos hd0
    have hne : Ad ⬝ᵥ d ≠ 0 := by
      intro h
      rw [hAd, dotProduct_comm] at h
      exact absurd h hpos.ne'
    have hsl : ∀ (c : ℝ) (u v : Fin n → ℝ), (c • u) ⬝ᵥ v = c * (u ⬝ᵥ v) := by
      intro c u v
      simp only [dotProduct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hden : (a • Ad) ⬝ᵥ d ≠ 0 := by
      rw [hsl a Ad d]
      exact mul_ne_zero ha0 hne
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul, hsl]
    rw [hcomm]
    field_simp [ha0, hd0]
    ring
