-- Prove2me | solution 1 for LimitedBFGS.SQN.exactStep_zero_gives_zero_dir
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T10:39:53.576826+00:00
-- url     : https://prove2.me/submissions/0707cb78-40b6-43bd-a0f8-6311c7a6367e

import Mathlib
import Definitions.Def_LimitedBFGS_SQN_pcgIter
import Theorems.Thm_LimitedBFGS_SQN_pcg_grad_direction_key

open Matrix
open LimitedBFGS.SQN

theorem solution {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (b : Fin n → ℝ) (H₀ : Matrix (Fin n) (Fin n) ℝ) (hH₀ : H₀.PosDef) (x₀ : Fin n → ℝ)
    (j : ℕ) (ha : exactStep A b (pcgIter A b H₀ x₀ j).x (pcgIter A b H₀ x₀ j).d = 0) :
    (pcgIter A b H₀ x₀ j).d = 0 := by
  classical
  by_cases hd0 : (pcgIter A b H₀ x₀ j).d = 0
  · exact hd0
  -- The direction is nonzero, so positive definiteness of `A` makes the denominator
  -- of the exact step positive.
  have hpos : 0 < (pcgIter A b H₀ x₀ j).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) :=
    hA.dotProduct_mulVec_pos hd0
  have hden : (pcgIter A b H₀ x₀ j).d ⬝ᵥ (A *ᵥ (pcgIter A b H₀ x₀ j).d) ≠ 0 := hpos.ne'
  -- A vanishing step with a nonzero denominator forces the step numerator to vanish.
  have hgd : grad A b (pcgIter A b H₀ x₀ j).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d = 0 := by
    have hnum : -(grad A b (pcgIter A b H₀ x₀ j).x
        ⬝ᵥ (pcgIter A b H₀ x₀ j).d)
        = 0 := by
      unfold exactStep at ha
      rw [div_eq_zero_iff] at ha
      rcases ha with h | h
      · exact h
      · exact absurd h hden
    exact neg_eq_zero.mp hnum
  -- The proved direction identity, instantiated at `j`, reads
  -- `g ⬝ᵥ d = -((H0 *ᵥ g) ⬝ᵥ g)`, so the `H0`-pairing of `g` vanishes.
  have hkey : grad A b (pcgIter A b H₀ x₀ j).x ⬝ᵥ (pcgIter A b H₀ x₀ j).d
      = -((H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) ⬝ᵥ grad A b (pcgIter A b H₀ x₀ j).x) :=
    pcg_grad_direction_key A hA b H₀ x₀ j
  have hself : (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) ⬝ᵥ grad A b (pcgIter A b H₀ x₀ j).x = 0 := by
    have hz : -(H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x ⬝ᵥ grad A b (pcgIter A b H₀ x₀ j).x) = 0 :=
      hkey.symm.trans (hgd ▸ rfl)
    exact neg_eq_zero.mp hz
  -- Positive definiteness of `H0` then forces the gradient itself to vanish.
  have hgnil : grad A b (pcgIter A b H₀ x₀ j).x = 0 := by
    by_contra hcon
    have hne : grad A b (pcgIter A b H₀ x₀ j).x ≠ 0 := hcon
    have hpos2 : 0 < grad A b (pcgIter A b H₀ x₀ j).x
        ⬝ᵥ (H₀ *ᵥ grad A b (pcgIter A b H₀ x₀ j).x) :=
      hH₀.dotProduct_mulVec_pos hne
    rw [dotProduct_comm] at hpos2
    rw [hself] at hpos2
    exact absurd hpos2 (not_lt_of_ge (by simp))
  cases j with
  | zero =>
      -- `d_0 = -(H0 *ᵥ g_0)` and `g_0 = 0`, so the initial direction vanishes.
      have h0 : pcgIter A b H₀ x₀ 0
          = ⟨x₀, -(H₀ *ᵥ grad A b x₀)⟩ := rfl
      have hxg : grad A b x₀ = 0 := by rwa [h0] at hgnil
      rw [h0]
      simp [hxg]
  | succ k =>
      -- At a successor index `d_{k+1} = -(H0 *ᵥ g_{k+1}) + beta • d_k`. With `g_{k+1} = 0`
      -- the first term vanishes and the `beta` numerator vanishes, so `beta = 0` whatever
      -- its denominator is, and `d_{k+1} = 0`.
      set stk := pcgIter A b H₀ x₀ k with hstk
      set dk := stk.d with hdk
      set bk := exactStep A b stk.x stk.d with hbk
      set xk := stk.x + bk • dk with hxk
      set gk := grad A b xk with hgk
      set Hk := H₀ *ᵥ gk with hHk
      set yk := gk - grad A b stk.x with hyk
      have hstep : pcgIter A b H₀ x₀ (k + 1)
          = ⟨xk, -Hk + ((yk ⬝ᵥ Hk) / (yk ⬝ᵥ dk)) • dk⟩ := by
        simp [pcgIter, hstk, hbk, hdk, hxk, hgk, hHk, hyk]
      -- The gradient at the successor index is `gk`, and it vanishes. `rwa` lets the
      -- structure projection collapse by defeq, which `rw` alone cannot do.
      have hxk_nil : grad A b xk = 0 := by
        have h1 := hgnil
        rwa [hstep] at h1
      have hgk_nil : gk = 0 := by rwa [← hgk] at hxk_nil
      have hHgk : H₀ *ᵥ gk = 0 := by rw [hgk_nil, Matrix.mulVec_zero]
      have hHk_nil : Hk = 0 := by rwa [← hHk] at hHgk
      rw [hstep]
      simp only [PCGState.d]
      -- With `gk = 0` the `H0`-multiple vanishes, so the `beta` numerator is `0` and
      -- Lean's total division makes `beta = 0` even when the denominator is `0`.
      rw [hHk_nil, dotProduct_zero, neg_zero, zero_div, zero_smul, add_zero]
