-- Prove2me | solution 1 for KServer.card_add_two_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:36:38.89783+00:00
-- url     : https://prove2.me/submissions/b3672dad-99fa-4be7-b24a-37f6e359c42a

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_card_add_two_inj

open KServer

/-- Spaces of exactly `k+2` points, the 2-evader problem: the Work Function Algorithm is
`k`-competitive.  This is the Extended Cost Lemma applied with `lam = k+1`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 2) (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by
  have hcard : Fintype.card (Fin k) ≤ Fintype.card M := by
    rw [Fintype.card_fin, hM]; omega
  obtain ⟨X₀⟩ := Function.Embedding.nonempty_iff_card_le.mpr hcard
  obtain ⟨c, hgrowth⟩ := workFnU_growth_card_add_two_inj k hk M hM C₀
  obtain ⟨A, hA0, hA⟩ :=
    extended_cost_lemma_injective k hk M C₀ (X₀ : Fin k → M) X₀.injective ((k : ℝ) + 1) c hgrowth
  refine ⟨A, hA0, ?_⟩
  have e : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
  rwa [e] at hA
