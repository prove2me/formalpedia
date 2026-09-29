-- Prove2me | solution 1 for KServer.wfa_potential_criterion
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T19:12:18.725408+00:00
-- url     : https://prove2.me/submissions/d1336c6f-be33-4f09-95f5-171c16845c4d

import Mathlib
import Definitions.Def_KServer_model
import Definitions.Def_KServer_work_function
import Theorems.Thm_KServer_wfa_cost_le_growth
import Theorems.Thm_KServer_workFn_approx_offlineCost

open KServer

private theorem wf_eq {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : workFunction C₀ σ X = workFn C₀ σ X := rfl

/-- **The potential-function criterion for the Work Function Algorithm.** -/
theorem solution (k : ℕ) (hk : 0 < k) (M : Type) [MetricSpace M] [Fintype M]
    (C₀ : Config k M) (C : ℝ) (hC : 0 ≤ C) (Φ : List M → ℝ)
    (hOP : ∀ (τ : List M) (X : Config k M), 0 ≤ Φ τ + (C + 1) * workFunction C₀ τ X)
    (hUP : ∀ (τ : List M) (s : M) (X : Config k M),
      workFunction C₀ (τ ++ [s]) X ≤ workFunction C₀ τ X + (Φ τ - Φ (τ ++ [s]))) :
    IsCompetitive (WFA hk C₀) C := by
  have hC1 : (0:ℝ) < C + 1 := by linarith
  refine ⟨Φ [], fun σ => ?_⟩
  have hgrowth : ∀ t : ℕ, t < σ.length → ∀ X : Config k M,
      workFunction C₀ (σ.take (t + 1)) X
        ≤ workFunction C₀ (σ.take t) X + (Φ (σ.take t) - Φ (σ.take (t + 1))) := by
    intro t ht X
    have hsplit : σ.take (t + 1) = σ.take t ++ [σ[t]'ht] := by
      rw [List.take_succ, List.getElem?_eq_getElem ht]
      rfl
    rw [hsplit]
    exact hUP (σ.take t) (σ[t]'ht) X
  have hmain := wfa_cost_le_growth k hk M C₀ σ
    (fun t => Φ (σ.take t) - Φ (σ.take (t + 1))) hgrowth
  have htel : (∑ t ∈ Finset.range σ.length, (Φ (σ.take t) - Φ (σ.take (t + 1))))
      = Φ (σ.take 0) - Φ (σ.take σ.length) :=
    Finset.sum_range_sub' (fun t => Φ (σ.take t)) σ.length
  have key : -Φ σ ≤ (C + 1) * offlineCost C₀ σ := by
    refine le_of_forall_pos_le_add ?_
    intro ε hε
    obtain ⟨X, hX⟩ := workFn_approx_offlineCost k hk M C₀ σ (ε / (C + 1)) (div_pos hε hC1)
    have h1 := hOP σ X
    rw [wf_eq] at h1
    have h3 : (C + 1) * workFn C₀ σ X ≤ (C + 1) * (offlineCost C₀ σ + ε / (C + 1)) :=
      mul_le_mul_of_nonneg_left hX (le_of_lt hC1)
    have h4 : (C + 1) * (offlineCost C₀ σ + ε / (C + 1))
        = (C + 1) * offlineCost C₀ σ + ε := by field_simp
    linarith
  have hconf : (WFA hk C₀).conf [] = C₀ := WFA_conf_nil hk C₀
  rw [hconf]
  simp only [htel, List.take_zero, List.take_length] at hmain
  linarith
