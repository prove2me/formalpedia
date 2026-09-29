-- Prove2me | solution 1 for KServer.work_function_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:36:37.655354+00:00
-- url     : https://prove2.me/submissions/0d65c2cd-ba1e-44b9-a89e-77053511b155

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_2k_inj
import Theorems.Thm_KServer_injective_or_covering
import Theorems.Thm_KServer_competitive_of_covering_config

open KServer

/-- The Work Function Algorithm is `(2k-1)`-competitive on every metric space.  This is the
Extended Cost Lemma applied with `lam = 2k`, together with the degenerate case in which the
space has fewer than `k` points. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type)
    [MetricSpace M] (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧
      IsCompetitive A (2 * (k : ℝ) - 1) := by
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  rcases injective_or_covering k M C₀ with ⟨X₀, hX₀⟩ | ⟨Y, hY⟩
  · obtain ⟨c, hgrowth⟩ := workFnU_growth_2k_inj k hk M C₀
    exact extended_cost_lemma_injective k hk M C₀ X₀ hX₀ (2 * (k : ℝ)) c hgrowth
  · exact competitive_of_covering_config k M C₀ Y hY (2 * (k : ℝ) - 1) (by linarith)
