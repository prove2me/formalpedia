-- Prove2me | solution 1 for KServer.workFnU_perm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-08-31T06:57:51.370069+00:00
-- url     : https://prove2.me/submissions/6b8d74aa-14de-4ce0-8b44-32eb3691a159

import Mathlib
import Definitions.Def_KServer_workfunctionU

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

/-- The unordered work function is invariant under relabelling its target. -/
theorem solution (k : ℕ) (M : Type) [MetricSpace M] (C₀ : Config k M) (σ : List M)
    (X : Config k M) (τ : Equiv.Perm (Fin k)) :
    workFnU C₀ σ (X ∘ τ) = workFnU C₀ σ X := by
  refine le_antisymm ?_ ?_
  · obtain ⟨π, hπ⟩ := wfU_exists C₀ σ X
    have hcomp : (X ∘ (τ : Equiv.Perm (Fin k))) ∘ ((τ⁻¹ * π : Equiv.Perm (Fin k)) :
        Fin k → Fin k) = X ∘ (π : Equiv.Perm (Fin k)) := by
      funext i; simp
    have h := wfU_le C₀ σ (X ∘ (τ : Equiv.Perm (Fin k))) (τ⁻¹ * π)
    rw [hcomp, hπ] at h
    exact h
  · obtain ⟨π, hπ⟩ := wfU_exists C₀ σ (X ∘ (τ : Equiv.Perm (Fin k)))
    have hcomp : X ∘ ((τ * π : Equiv.Perm (Fin k)) : Fin k → Fin k)
        = (X ∘ (τ : Equiv.Perm (Fin k))) ∘ (π : Equiv.Perm (Fin k)) := by
      funext i; simp
    have h := wfU_le C₀ σ X (τ * π)
    rw [hcomp, hπ] at h
    exact h
