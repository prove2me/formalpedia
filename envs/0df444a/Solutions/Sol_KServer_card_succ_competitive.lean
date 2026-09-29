-- Prove2me | solution 1 for KServer.card_succ_competitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:26:21.766692+00:00
-- url     : https://prove2.me/submissions/53be1dd4-b15f-402b-9e1e-631b3d641c93

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_extended_cost_lemma_injective
import Theorems.Thm_KServer_workFnU_growth_card_succ_inj

open KServer

/-- Spaces of exactly `k+1` points: the Work Function Algorithm is `k`-competitive.
This is the Extended Cost Lemma applied with `lam = k+1`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    [Fintype M] (hM : Fintype.card M = k + 1) (C₀ : Config k M) :
    ∃ A : OnlineAlgorithm k M, A.conf [] = C₀ ∧ IsCompetitive A (k : ℝ) := by
  classical
  -- on a space of `k+1` points an injective configuration exists
  have hpos : 0 < Fintype.card M := by rw [hM]; omega
  obtain ⟨p⟩ := Fintype.card_pos_iff.mp hpos
  have hc : Fintype.card {x : M // x ≠ p} = k := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, hM]; omega
  set X₀ : Config k M := fun i => ((Fintype.equivFinOfCardEq hc).symm i : M) with hX₀def
  have hX₀ : Function.Injective X₀ := by
    intro a b hab
    exact (Fintype.equivFinOfCardEq hc).symm.injective (Subtype.ext hab)
  obtain ⟨c, hgrowth⟩ := workFnU_growth_card_succ_inj k hk M hM C₀
  obtain ⟨A, hA0, hA⟩ :=
    extended_cost_lemma_injective k hk M C₀ X₀ hX₀ ((k : ℝ) + 1) c hgrowth
  refine ⟨A, hA0, ?_⟩
  have e : (k : ℝ) + 1 - 1 = (k : ℝ) := by ring
  rwa [e] at hA
