-- Prove2me | solution 1 for InfoLossLAR.WorstCase.RegevSearch.coherent_shared_pool_fourier_sampler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-21T05:32:20.349908+00:00
-- url     : https://prove2.me/submissions/68c6cc01-99bf-4eec-b807-33d377995644
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_uniform_physical_fourier_row
import Theorems.Thm_InfoLossLAR_WorstCase_RegevSearch_iterate_uniform_fourier_row
set_option autoImplicit false
set_option maxHeartbeats 5500000
set_option maxRecDepth 14000
set_option backward.isDefEq.respectTransparency false
open QAlgorithms.Complexity InfoLossLAR.WorstCase InfoLossLAR.WorstCase.RegevSketch RegevLWE.GaussConv
open scoped BigOperators Classical

open InfoLossLAR.WorstCase.RegevSearch

theorem solution
    (S : Set ℕ) (hS : S.Infinite) (hpos : ∀ n ∈ S, 1 ≤ n)
    (C : MFamily) (hC : IsMQPT C) (P : Polynomial ℕ) (N : ℕ)
    (hcopy : ∀ calls : Polynomial ℕ, ∃ e : ℕ → ℝ,
      Negligible e ∧ SharedPoolCoherence.CopyBudget C P calls N S e)
    (hschedule : ∀ {n : ℕ}, 2 ≤ n →
      ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
      ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∃ D : Matrix (Fin n) (Fin n) ℤ, D.det ≠ 0 ∧ inputModule D = inputModule B ∧
    ∃ W : ℚ, W = max (((n+1 : ℕ) : ℚ) * (1 + ∑ i, ∑ j, |(D i j : ℚ)|)) (r * (famσ n : ℚ)) ∧
    ∃ h : ℕ, h ≤ 5*n+2 ∧
      (∀ j ≤ h, Real.sqrt 2 * (famq n : ℝ) * smoothingParam (inputModule B) (smoothingError n) <
        (W : ℝ) / 2^j) ∧
      Real.sqrt n / (Real.sqrt 2 * (r : ℝ)) ≤ (famσ n : ℝ)/(2*((W : ℝ)/2^h))) :
    ∃ H : MFamily, IsMQPT H ∧ ∃ e : ℕ → ℝ, Negligible e ∧
      ∃ N' : ℕ, ∀ n ∈ S, N' ≤ n →
        ∀ B : Matrix (Fin n) (Fin n) ℤ, B.det ≠ 0 →
        ∀ r : ℚ, 0 < r → dgsThreshold B ≤ (r : ℝ) →
        ∀ k : ℕ, ∃ b : ℕ,
          gridAdequate B (r : ℝ) (2^b) ∧
          outputProb H (dgsInput B r 1 k) (fun out => ∃ z : Fin n → ℤ, encVec encI z <+: out) = 1 ∧
          ∀ T : Finset (Fin n → ℤ),
            |outputProb H (dgsInput B r 1 k) (fun out => ∃ z ∈ T, encVec encI z <+: out) -
              fourierEvent B (r : ℝ) (2^b) T| ≤ e n + 1/(4*((k:ℝ)+1)) := by
  exact iterate_uniform_fourier_row S C P N hcopy (uniform_physical_fourier_row C hC P)
