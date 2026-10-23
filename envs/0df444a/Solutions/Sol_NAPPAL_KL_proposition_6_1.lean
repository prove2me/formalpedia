-- Prove2me | solution 1 for NAPPAL.KL.proposition_6_1
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-23T00:30:59.856736+00:00
-- url     : https://prove2.me/submissions/ec394bc1-b44a-4ce8-ac76-229e9d078e03

import Mathlib
import Definitions.Def_NAPPAL_KL_Setting
import Theorems.Thm_NAPPAL_KL_proposition_6_1_case_1

open NAPPAL.KL in
theorem solution {n d m : ℕ} (P : Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ) (u : ℕ → E n) (v : ℕ → E d)
    (p : ℕ → E m) (hrun : RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p) (wbar : W n d m)
    (hcl : MapClusterPt wbar Filter.atTop (wseq u v p)) (η ν κ2 : ℝ)
    (hKL : HasKLAt P γ wbar (1 / 2) η ν κ2) :
    ∃ κ1 η' ν' : ℝ, VPEB P γ (wseq u v p) wbar κ1 η' ν' := by
  obtain ⟨c5, hc5, hcase⟩ :=
    proposition_6_1_case_1 P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun wbar hcl η ν κ2 hKL
  obtain ⟨-, -, hη, hν, hκ2, -⟩ := hKL
  refine ⟨(κ2 * c5) ^ 2, η, ν, by positivity, hη, hν, fun k hd hhi => ?_⟩
  by_cases hlo : augLag P γ wbar < augLag P γ (wseq u v p (k + 1))
  · exact (hcase k hd hlo hhi).2
  · push_neg at hlo
    have : 0 ≤ (κ2 * c5) ^ 2 * wdist (wseq u v p k) (wseq u v p (k + 1)) ^ 2 := by positivity
    linarith
