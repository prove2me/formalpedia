-- Prove2me | solution 1 for KServer.ck_potential_offset
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T21:15:13.435124+00:00
-- url     : https://prove2.me/submissions/afe932af-ddb8-4409-b152-6a2384583410

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_lipschitz

open KServer

private theorem lip3' {M : Type} [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (a b c : M) (X : Config 3 M) (Δ : ℝ) (hΔ : ∀ u v : M, dist u v ≤ Δ) :
    workFnU C₀ σ ![a, b, c] ≤ workFnU C₀ σ X + 3 * Δ := by
  have hmc : moveCost X (![a, b, c] : Config 3 M) ≤ 3 * Δ := by
    unfold moveCost
    rw [Fin.sum_univ_three]
    have h0 : dist (X 0) a ≤ Δ := hΔ (X 0) a
    have h1 : dist (X 1) b ≤ Δ := hΔ (X 1) b
    have h2 : dist (X 2) c ≤ Δ := hΔ (X 2) c
    show dist (X 0) a + dist (X 1) b + dist (X 2) c ≤ 3 * Δ
    linarith
  have h := workFnU_lipschitz 3 (by norm_num) M C₀ σ ![a, b, c] X
  linarith

/-- **The offset property of the Coester–Koutsoupias potential.** -/
theorem solution (M : Type) [MetricSpace M] (C₀ : Config 3 M) (σ : List M)
    (Δ : ℝ) (hΔ : ∀ u v : M, dist u v ≤ Δ) (bar : M → M) (x y z : M) (X : Config 3 M) :
    workFnU C₀ σ ![x, y, z] + workFnU C₀ σ ![bar x, y, z]
      + workFnU C₀ σ ![bar y, bar y, z] + workFnU C₀ σ ![bar z, bar z, bar z]
      ≤ 4 * workFnU C₀ σ X + 12 * Δ := by
  have h0 := lip3' C₀ σ x y z X Δ hΔ
  have h1 := lip3' C₀ σ (bar x) y z X Δ hΔ
  have h2 := lip3' C₀ σ (bar y) (bar y) z X Δ hΔ
  have h3 := lip3' C₀ σ (bar z) (bar z) (bar z) X Δ hΔ
  linarith
