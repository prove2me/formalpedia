-- Prove2me | solution 1 for NAPPAL.Subreg.lemma_6_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T20:02:34.415743+00:00
-- url     : https://prove2.me/submissions/d6ed0e18-ed0a-488a-bf9f-5eca6b1cc359
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_NAPPAL_Subreg_Setting
import Theorems.Thm_NAPPAL_Subreg_lemma_6_1_uniform

theorem solution {n d m : ℕ} (P : NAPPAL.KL.Problem n d m) (LG LH L0 : ℝ) (LOmj : Fin m → ℝ)
    (LK : ℝ) (K : NAPPAL.KL.E n → ℝ) (β γ σ : ℝ) (δ ε : ℕ → ℝ)
    (u : ℕ → NAPPAL.KL.E n) (v : ℕ → NAPPAL.KL.E d) (p : ℕ → NAPPAL.KL.E m)
    (hrun : NAPPAL.Subreg.RunHyp P LG LH L0 LOmj LK K β γ σ δ ε u v p)
    (wbar : NAPPAL.KL.W n d m) (hstat : NAPPAL.KL.IsStationary P γ wbar) :
    ∃ c6 : ℝ, 0 < c6 ∧ ∀ k : ℕ,
      NAPPAL.KL.augLag P γ (NAPPAL.KL.wseq u v p (k+1)) - NAPPAL.KL.augLag P γ wbar ≤
        c6 * (NAPPAL.KL.wdist wbar (NAPPAL.KL.wseq u v p (k+1)) ^ 2 +
          NAPPAL.KL.wdist (NAPPAL.KL.wseq u v p k) (NAPPAL.KL.wseq u v p (k+1)) ^ 2) := by
  obtain ⟨c6, hc6, h⟩ :=
    NAPPAL.Subreg.lemma_6_1_uniform P LG LH L0 LOmj LK K β γ σ δ ε u v p hrun
  exact ⟨c6, hc6, h wbar hstat⟩
