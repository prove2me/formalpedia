-- Prove2me | solution 1 for Lubbecke2005.Discretization.binary_points_are_vertices
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:50:26.077591+00:00
-- url     : https://prove2.me/submissions/17770a14-013d-44b8-adef-dd55a58ab67e

import Mathlib
import Definitions.Def_Lubbecke2005_Discretization_Polyhedron
open Lubbecke2005.Discretization

theorem solution {m n : ℕ} (D : Matrix (Fin m) (Fin n) ℚ)
    (d : Fin m → ℚ)
    (hX : ∀ x ∈ integerPoints D d, ∀ j, x j ∈ Set.Icc (0 : ℝ) 1) :
    ∀ x ∈ integerPoints D d,
      x ∈ Set.extremePoints ℝ (convexHull ℝ (integerPoints D d)) := by
  intro x hx
  let cube : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Icc (0 : ℝ) 1)
  have hsub : convexHull ℝ (integerPoints D d) ⊆ cube := by
    apply convexHull_min
    · intro y hy j _
      exact hX y hy j
    · exact convex_pi (fun _ _ => convex_Icc 0 1)
  have hext : x ∈ cube.extremePoints ℝ := by
    dsimp [cube]
    rw [extremePoints_pi]
    intro j _
    rw [Set.extremePoints_Icc (by norm_num : (0 : ℝ) ≤ 1)]
    obtain ⟨z, hzx⟩ := hx.2
    have hj := hX x hx j
    rw [hzx] at hj ⊢
    change (0 ≤ (z j : ℝ) ∧ (z j : ℝ) ≤ 1) at hj
    have h0 : 0 ≤ z j := by exact_mod_cast hj.1
    have h1 : z j ≤ 1 := by exact_mod_cast hj.2
    have hz : z j = 0 ∨ z j = 1 := by omega
    rcases hz with hz | hz <;> simp [castVec, hz]
  exact inter_extremePoints_subset_extremePoints_of_subset hsub
    ⟨subset_convexHull ℝ _ hx, hext⟩
