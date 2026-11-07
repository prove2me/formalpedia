-- Prove2me | solution 1 for KumarSeidman.Reentrant.example1_case1_unstable
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T17:24:37.907663+00:00
-- url     : https://prove2.me/submissions/15928868-1479-4210-9660-39d08f981806

import Mathlib
import Definitions.Def_KumarSeidman_Reentrant_System
import Definitions.Def_KumarSeidman_Reentrant_Trajectory
import Definitions.Def_KumarSeidman_Reentrant_Clearing
import Definitions.Def_KumarSeidman_Reentrant_Example1
import Theorems.Thm_KumarSeidman_Reentrant_example1_case1_exists
import Theorems.Thm_KumarSeidman_Reentrant_example1_case1_all_unbounded

open KumarSeidman.Reentrant in
theorem solution (τ : Fin 4 → ℝ) (hτ : ∀ k, 0 < τ k)
    (h3 : 1 < τ 1 + τ 3) (h4 : τ 0 + τ 3 < 1) (h5 : τ 1 + τ 2 < 1)
    (δ : Fin 4 → ℝ) (hδ : ∀ k, 0 < δ k) :
    ∃ ξ₀ : ℝ, ∀ ξ : ℝ, 0 < ξ → ξ₀ ≤ ξ →
      (∃ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T ∧ Ex1Initial T ξ) ∧
      ∀ T : Trajectory (ex1 τ hτ δ (fun k => (hδ k).le)),
        IsClearing (ex1 τ hτ δ (fun k => (hδ k).le)) T → Ex1Initial T ξ →
          ∀ C : ℝ, ∃ t : ℝ, 0 ≤ t ∧ C < T.x (ex1Buf 0) t := by
  obtain ⟨a, ha⟩ := example1_case1_exists τ hτ h3 h4 h5 δ hδ
  obtain ⟨b, hb⟩ := example1_case1_all_unbounded τ hτ h3 h4 h5 δ hδ
  exact ⟨max a b, fun ξ hξ h => ⟨ha ξ hξ ((le_max_left a b).trans h),
    hb ξ hξ ((le_max_right a b).trans h)⟩⟩
