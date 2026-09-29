-- Prove2me | solution 1 for KServer.workFnU_dual_quasiconvex
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T05:45:19.031735+00:00
-- url     : https://prove2.me/submissions/0aff452c-e67e-4381-93c2-9cf2d721468f

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFnU_quasiconvex

open KServer

/-- **The dual functional inherits quasiconvexity, with the same alignment.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (s : M) (X Y : Config k M) :
    ∃ π : Equiv.Perm (Fin k), ∀ t : Finset (Fin k),
      (workFnU C₀ σ (fun i => if i ∈ t then X i else Y (π i))
          - ∑ i, dist s ((fun i => if i ∈ t then X i else Y (π i)) i))
        + (workFnU C₀ σ (fun i => if i ∈ t then Y (π i) else X i)
          - ∑ i, dist s ((fun i => if i ∈ t then Y (π i) else X i) i))
      ≤ (workFnU C₀ σ X - ∑ i, dist s (X i))
        + (workFnU C₀ σ Y - ∑ i, dist s (Y i)) := by
  obtain ⟨π, hπ⟩ := workFnU_quasiconvex k hk M C₀ σ X Y
  refine ⟨π, fun t => ?_⟩
  have hq := hπ t
  have hsum : (∑ i, dist s ((fun i => if i ∈ t then X i else Y (π i)) i))
      + (∑ i, dist s ((fun i => if i ∈ t then Y (π i) else X i) i))
      = (∑ i, dist s (X i)) + ∑ i, dist s (Y i) := by
    have hperm : (∑ i, dist s (Y (π i))) = ∑ i, dist s (Y i) :=
      Fintype.sum_equiv π (fun i => dist s (Y (π i))) (fun i => dist s (Y i)) (fun i => rfl)
    rw [← hperm, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i ∈ t <;> simp [hi, add_comm]
  linarith
