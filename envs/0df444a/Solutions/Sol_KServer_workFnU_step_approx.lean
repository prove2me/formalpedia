-- Prove2me | solution 1 for KServer.workFnU_step_approx
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T07:01:06.12168+00:00
-- url     : https://prove2.me/submissions/478a998b-35c9-4cee-9955-7c4bae28faa4

import Mathlib
import Definitions.Def_KServer_workfunctionU
import Theorems.Thm_KServer_workFn_step_approx

open KServer

private theorem wfU_le {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (π : Equiv.Perm (Fin k)) :
    workFnU C₀ σ X ≤ workFn C₀ σ (X ∘ π) :=
  ciInf_le (Finite.bddBelow_range _) π

private theorem wfU_exists {k : ℕ} {M : Type} [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) : ∃ π : Equiv.Perm (Fin k), workFn C₀ σ (X ∘ π) = workFnU C₀ σ X :=
  exists_eq_ciInf_of_finite

private theorem mc_perm {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π : Equiv.Perm (Fin k))) (Z ∘ (π : Equiv.Perm (Fin k)))
      = moveCost Y Z := by
  unfold moveCost
  exact Fintype.sum_equiv π (fun i => dist (Y (π i)) (Z (π i))) (fun j => dist (Y j) (Z j))
    (fun i => rfl)

private theorem mc_reindex {k : ℕ} {M : Type} [MetricSpace M] (Y Z : Config k M)
    (π : Equiv.Perm (Fin k)) :
    moveCost (Y ∘ (π⁻¹ : Equiv.Perm (Fin k))) Z = moveCost Y (Z ∘ π) := by
  unfold moveCost
  refine (Fintype.sum_equiv π (fun j => dist (Y j) ((Z ∘ π) j))
    (fun i => dist ((Y ∘ (π⁻¹ : Equiv.Perm (Fin k))) i) (Z i)) ?_).symm
  intro j
  simp

/-- **One step of the unordered work-function recurrence, lower half.** -/
theorem solution (k : ℕ) (hk : 1 ≤ k) (M : Type) [MetricSpace M]
    (C₀ : Config k M) (σ : List M) (r : M) (Z : Config k M) (ε : ℝ) (hε : 0 < ε) :
    ∃ Y : Config k M, (∃ i, Y i = r) ∧
      workFnU C₀ σ Y + moveCost Y Z ≤ workFnU C₀ (σ ++ [r]) Z + ε := by
  obtain ⟨π, hπ⟩ := wfU_exists C₀ (σ ++ [r]) Z
  obtain ⟨Y', hY'cov, hY'⟩ := workFn_step_approx k hk M C₀ σ r (Z ∘ π) ε hε
  refine ⟨Y' ∘ (π⁻¹ : Equiv.Perm (Fin k)), ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hY'cov
    exact ⟨π i, by simpa using hi⟩
  · have hcomp : (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) ∘ (π : Equiv.Perm (Fin k)) = Y' := by
      funext i; simp
    have h1 : workFnU C₀ σ (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) ≤ workFn C₀ σ Y' := by
      have := wfU_le C₀ σ (Y' ∘ (π⁻¹ : Equiv.Perm (Fin k))) π
      rwa [hcomp] at this
    have h2 := mc_reindex Y' Z π
    rw [← hπ]
    linarith
