-- Prove2me | solution 1 for KServer.workFnU_mcshane_request
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-01T06:01:44.708337+00:00
-- url     : https://prove2.me/submissions/46077af3-8f5e-4c72-aa31-abd98d921011

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Definitions.Def_KServer_antipodal_extension
import Theorems.Thm_KServer_workFnU_mcshane_envelope
import Theorems.Thm_KServer_workFnU_resolves

open KServer

private theorem sum_diff_single {k : ℕ} (F G : Fin k → ℝ) (p : Fin k)
    (h : ∀ i, i ≠ p → F i = G i) : ∑ i, F i - ∑ i, G i = F p - G p := by
  classical
  rw [← Finset.add_sum_erase _ F (Finset.mem_univ p),
    ← Finset.add_sum_erase _ G (Finset.mem_univ p),
    Finset.sum_congr rfl (fun i hi => h i (Finset.ne_of_mem_erase hi))]
  ring

/-- **The envelope minimizer can be taken to contain the last request.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M] (Δ : ℝ)
    (hΔ0 : 0 < Δ) (hΔ : ∀ x y : M, dist x y ≤ Δ)
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k (M ⊕ M)) :
    ∃ X : Config k M, (∃ j, X j = r) ∧
      @workFnU k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ)
          (fun i => Sum.inl (C₀ i)) ((σ ++ [r]).map Sum.inl) Z
        = workFnU C₀ (σ ++ [r]) X
          + @moveCost k (M ⊕ M) (antipodalExtension M Δ hΔ0 hΔ) (fun i => Sum.inl (X i)) Z := by
  letI : MetricSpace (M ⊕ M) := antipodalExtension M Δ hΔ0 hΔ
  obtain ⟨hle, X, hX⟩ := workFnU_mcshane_envelope k hk M Δ hΔ0 hΔ C₀ (σ ++ [r]) Z
  obtain ⟨j, hj⟩ := workFnU_resolves k hk M C₀ σ r X
  set X' : Config k M := Function.update X j r with hX'
  have hcov : ∃ l, X' l = r := ⟨j, by rw [hX']; exact Function.update_self _ _ _⟩
  refine ⟨X', hcov, le_antisymm (by simpa using hle X') ?_⟩
  -- the movement costs differ only at the coordinate j
  have hmc : @moveCost k (M ⊕ M) _ (fun i => Sum.inl (X' i)) Z
      - @moveCost k (M ⊕ M) _ (fun i => Sum.inl (X i)) Z
      = dist (Sum.inl r : M ⊕ M) (Z j) - dist (Sum.inl (X j) : M ⊕ M) (Z j) := by
    have h := sum_diff_single (fun i => dist (Sum.inl (X' i) : M ⊕ M) (Z i))
      (fun i => dist (Sum.inl (X i) : M ⊕ M) (Z i)) j ?_
    · have hXj : X' j = r := by rw [hX']; exact Function.update_self _ _ _
      unfold moveCost
      rw [h, hXj]
    · intro i hi
      show dist (Sum.inl (X' i) : M ⊕ M) (Z i) = dist (Sum.inl (X i) : M ⊕ M) (Z i)
      have h2 : X' i = X i := by rw [hX']; exact Function.update_of_ne hi _ _
      rw [h2]
  have htri : dist (Sum.inl r : M ⊕ M) (Z j)
      ≤ dist r (X j) + dist (Sum.inl (X j) : M ⊕ M) (Z j) := by
    have h := dist_triangle (Sum.inl r : M ⊕ M) (Sum.inl (X j)) (Z j)
    have he : dist (Sum.inl r : M ⊕ M) (Sum.inl (X j)) = dist r (X j) := rfl
    rw [he] at h
    exact h
  -- resolve X to X' and absorb the moved coordinate by the triangle inequality
  rw [hX]
  rw [hj]
  have hXj' : workFnU C₀ (σ ++ [r]) (Function.update X j r) = workFnU C₀ (σ ++ [r]) X' := by
    rw [hX']
  rw [hXj']
  linarith
