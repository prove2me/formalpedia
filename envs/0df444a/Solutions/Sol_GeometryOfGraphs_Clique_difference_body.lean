-- Prove2me | solution 1 for GeometryOfGraphs.Clique.difference_body
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T20:43:48.191219+00:00
-- url     : https://prove2.me/submissions/b37c3fde-7171-43cf-8478-0a4f1e6c34cf

import Mathlib
import Definitions.Def_GeometryOfGraphs_Clique_isoDim

set_option autoImplicit false
open GeometryOfGraphs.Clique

theorem solution {n d : ℕ} (hn : 0 < n) (N : (Fin d → ℝ) → ℝ)
    (hN : IsNormFun N) (x : Fin n → (Fin d → ℝ))
    (hx : ∀ i j, i ≠ j → N (x i - x j) = 1)
    (u v : Fin d → ℝ)
    (hu : u ∈ convexHull ℝ (Set.range x))
    (hv : v ∈ convexHull ℝ (Set.range x)) :
    N (u - v) ≤ 1 := by
  obtain ⟨h0, hsep, hhom, htri⟩ := hN
  have hN0 : N 0 = 0 := by simpa using hhom 0 0
  have hneg : ∀ y, N (-y) = N y := fun y => by
    have := hhom (-1) y
    simpa using this
  have hball : ∀ c : Fin d → ℝ, Convex ℝ {y | N (y - c) ≤ 1} := by
    intro c y hy z hz a b ha hb hab
    simp only [Set.mem_setOf_eq] at *
    have e : a • y + b • z - c = a • (y - c) + b • (z - c) := by
      have hc : c = (a + b) • c := by rw [hab, one_smul]
      conv_lhs => rw [hc]
      simp only [smul_sub, add_smul]
      abel
    rw [e]
    calc N (a • (y - c) + b • (z - c)) ≤ N (a • (y - c)) + N (b • (z - c)) := htri _ _
      _ = a * N (y - c) + b * N (z - c) := by
          rw [hhom, hhom, abs_of_nonneg ha, abs_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by rw [mul_one, mul_one, hab]
  have hxx : ∀ i j, N (x i - x j) ≤ 1 := by
    intro i j
    by_cases h : i = j
    · subst h
      simp [hN0]
    · exact (hx i j h).le
  have step1 : ∀ i, ∀ w ∈ convexHull ℝ (Set.range x), N (w - x i) ≤ 1 := by
    intro i w hw
    have : convexHull ℝ (Set.range x) ⊆ {y | N (y - x i) ≤ 1} :=
      convexHull_min (by rintro _ ⟨j, rfl⟩; exact hxx j i) (hball _)
    exact this hw
  have step2 : convexHull ℝ (Set.range x) ⊆ {y | N (y - v) ≤ 1} := by
    refine convexHull_min ?_ (hball v)
    rintro _ ⟨j, rfl⟩
    have := step1 j v hv
    have h2 : x j - v = -(v - x j) := by abel
    show N (x j - v) ≤ 1
    rw [h2, hneg]
    exact this
  exact step2 hu
