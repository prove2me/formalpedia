-- Prove2me | solution 1 for InfoLossLAR.WorstCase.corollary_10_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @BoomShaKaLaaaKa
-- created : 2026-11-13T16:13:03.728888+00:00
-- url     : https://prove2.me/submissions/0c711e04-2ebb-4d0c-917f-30238433004d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_InfoLossLAR_WorstCase_theorem_9_9
import Theorems.Thm_InfoLossLAR_WorstCase_fixed_family_gaussian_advantage_transfer
import Theorems.Thm_InfoLossLAR_WorstCase_fixed_family_gaussian_lwe_worst_case

set_option autoImplicit false

open QAlgorithms.Complexity InfoLossLAR.WorstCase

theorem solution :
    ∃ C k : ℕ, ∀ D : Family, IsQPT D →
      ∀ t : ℕ → ℕ, (∀ lam, 1 ≤ t lam) → PolyBoundedFn t →
        ∀ c : ℕ, ∀ S : Set ℕ, S.Infinite → (∀ lam ∈ S, 1 ≤ lam) →
          (∀ lam ∈ S, (lam : ℝ) ^ (-(c : ℝ)) ≤ famAdvLAR D lam (t lam)) →
            (∃ A : Family, IsQPT A ∧ ∀ lam ∈ S,
              SolvesGapSVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k)) ∧
            (∃ A : MFamily, IsMQPT A ∧ ∀ lam ∈ S,
              SolvesSIVP A (famN lam)
                ((C : ℝ) * (famq lam : ℝ) * Real.logb 2 ((lam : ℝ) + 2) ^ k))  := by
  have hAFT : AdmitsFixedOrderGaussianAFT famInput famq famd (fun _ => 1)
      (fun lam => (famσ lam : ℝ)) famLabel := by
    intro c hc
    obtain ⟨C_R, hC_R, negl_R, hnegl_R, horder⟩ := theorem_9_9 (4 * c + 267)
    obtain ⟨m, sampler, hPPT, hinvertible, hquantitative, haccuracy⟩ :=
      horder c hc (by omega) c (by omega)
    exact ⟨m, sampler, hPPT, hinvertible, haccuracy⟩
  obtain ⟨C, k, hC, hGaussian⟩ := fixed_family_gaussian_lwe_worst_case
  refine ⟨C, k, ?_⟩
  intro D hD t ht htp c S hS hpositive hLAR
  obtain ⟨B, hB, hOnce, b, lam₀, htransfer⟩ :=
    fixed_family_gaussian_advantage_transfer hAFT D hD t ht htp c
  apply hGaussian B hB t ht htp b S hS hpositive
  refine ⟨lam₀, ?_⟩
  intro lam hlam hlarge
  exact htransfer lam hlarge (hpositive lam hlam) (hLAR lam hlam)

