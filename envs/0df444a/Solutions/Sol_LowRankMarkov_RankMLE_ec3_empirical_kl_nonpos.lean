-- Prove2me | solution 1 for LowRankMarkov.RankMLE.ec3_empirical_kl_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-20T20:24:36.333998+00:00
-- url     : https://prove2.me/submissions/d78c82e3-f8a0-40f2-bcbb-8138ade76b7f

import Mathlib
import Definitions.Def_LowRankMarkov_RankMLE_Chain
import Definitions.Def_LowRankMarkov_RankMLE_Setting

open LowRankMarkov.RankMLE

theorem solution {p r n : ℕ} (α β : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (P : Matrix (Fin p) (Fin p) ℝ) (hP : IsStochastic P) (hrank : P.rank = r)
    (hmin : Minorated α β P) (x : Fin (n + 1) → Fin p) (Q : Matrix (Fin p) (Fin p) ℝ)
    (hQ : IsRankMLE α β r x Q) :
    empKL x P Q ≤ 0 := by
  have hfeas : RankFeasible α β r P := ⟨hP.2, hmin, hrank.le⟩
  have := hQ.2 P hfeas
  unfold empKL
  linarith
