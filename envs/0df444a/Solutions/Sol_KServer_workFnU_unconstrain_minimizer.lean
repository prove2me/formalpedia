-- Prove2me | solution 1 for KServer.workFnU_unconstrain_minimizer
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T22:49:00.249971+00:00
-- url     : https://prove2.me/submissions/6451736c-0b3c-45ed-ab6f-35db770c67b9

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_quasiconvex

open KServer

/-- **Unconstraining a minimizer**: a cheapest configuration serving `r` becomes a
globally cheapest configuration by moving the server that sits on `r`. -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Y : Config k M) (j : Fin k) (hj : Y j = r)
    (hY : ∀ W : Config k M, (∃ l, W l = r) → workFnU C₀ σ Y ≤ workFnU C₀ σ W)
    (Z : Config k M) (hZ : ∀ W : Config k M, workFnU C₀ σ Z ≤ workFnU C₀ σ W) :
    ∃ z : M, ∀ W : Config k M,
      workFnU C₀ σ (Function.update Y j z) ≤ workFnU C₀ σ W := by
  classical
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ Y Z
  refine ⟨Z (π j), ?_⟩
  have hmem : ∀ i : Fin k, i ∈ (Finset.univ.erase j) ↔ i ≠ j := by
    intro i; simp [Finset.mem_erase]
  have h := hπ (Finset.univ.erase j)
  have hA : (fun i => if i ∈ Finset.univ.erase j then Y i else Z (π i))
      = Function.update Y j (Z (π j)) := by
    funext i
    by_cases hi : i = j
    · subst hi
      rw [if_neg (by simp [hmem]), Function.update_self]
    · rw [if_pos ((hmem i).mpr hi), Function.update_of_ne hi]
  rw [hA] at h
  have hcov : ∃ l, (fun i => if i ∈ Finset.univ.erase j then Z (π i) else Y i) l = r := by
    refine ⟨j, ?_⟩
    simp only
    rw [if_neg (by simp [hmem]), hj]
  have hge := hY _ hcov
  intro W
  have hZW := hZ W
  linarith
