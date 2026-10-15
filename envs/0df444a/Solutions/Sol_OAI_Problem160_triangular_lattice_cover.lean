-- Prove2me | solution 1 for OAI.Problem160.triangular_lattice_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:43:44.223785+00:00
-- url     : https://prove2.me/submissions/28fbe7c4-2749-485c-82b0-e998b019f934

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Covering.lean:L45-L91
-- (upload_full_project.md Phase 4): solution for node OAI.Problem160.triangular_lattice_cover. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_PlaneColoring
import Definitions.Def_OAI_Geometry_PlaneColoring_Lattice
import Definitions.Def_OAI_Geometry_PlaneColoring_Basic
import Definitions.Def_OAI_Geometry_PlaneColoring_Metric

-- ---- inline helpers from OAI.Geometry.PlaneColoring.Covering ----
namespace OAI

noncomputable section

namespace Problem160

private theorem triangular_wedge_bound (s x y : ℝ)
    (hs : 0 < s) (hsq : s ^ 2 = 3)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hxy : s * y ≤ 1 - x) :
    x ^ 2 + y ^ 2 ≤ 1 / 3 := by
  have hnonneg : 0 ≤ (1 - x) - s * y := by linarith
  have hplus : 0 ≤ (1 - x) + s * y := by
    nlinarith [mul_nonneg (le_of_lt hs) hy0]
  have hprod := mul_nonneg hnonneg hplus
  have hxprod := mul_nonneg hx0 (show 0 ≤ 1 / 2 - x by linarith)
  nlinarith [sq_nonneg (s * y), sq_nonneg y]

private theorem triangular_rectangle_cover (s x y : ℝ)
    (hs : 0 < s) (hsq : s ^ 2 = 3)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hy0 : 0 ≤ y) (hy1 : y ≤ s / 2) :
    x ^ 2 + y ^ 2 ≤ 1 / 3 ∨
    (x - 1) ^ 2 + y ^ 2 ≤ 1 / 3 ∨
    (x - 1 / 2) ^ 2 + (y - s / 2) ^ 2 ≤ 1 / 3 := by
  by_cases hx : x ≤ 1 / 2
  · by_cases hxy : s * y ≤ 1 - x
    · exact Or.inl (triangular_wedge_bound s x y hs hsq hx0 hx hy0 hxy)
    · right; right
      have h := triangular_wedge_bound s (1 / 2 - x) (s / 2 - y) hs hsq
        (by linarith) (by linarith) (by linarith) (by nlinarith)
      nlinarith
  · by_cases hxy : s * y ≤ x
    · right; left
      have h := triangular_wedge_bound s (1 - x) y hs hsq
        (by linarith) (by linarith) hy0 (by linarith)
      nlinarith
    · right; right
      have h := triangular_wedge_bound s (x - 1 / 2) (s / 2 - y) hs hsq
        (by linarith) (by linarith) (by linarith) (by nlinarith)
      nlinarith

end Problem160

end

end OAI

-- ---- hoisted node ----
open OAI OAI.Problem160

theorem solution (x y : ℝ) :
    ∃ m n : ℤ,
      (x - ((m : ℝ) + (n : ℝ) / 2)) ^ 2 +
        (y - Real.sqrt 3 * (n : ℝ) / 2) ^ 2 ≤ 1 / 3 := by
  let s : ℝ := Real.sqrt 3
  have hs : 0 < s := Real.sqrt_pos.2 (by norm_num)
  have hsq : s ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  let n : ℤ := ⌊2 * y / s⌋
  let m : ℤ := ⌊x - (n : ℝ) / 2⌋
  let u : ℝ := x - ((m : ℝ) + (n : ℝ) / 2)
  let v : ℝ := y - s * (n : ℝ) / 2
  have hn0 : (n : ℝ) ≤ 2 * y / s := Int.floor_le _
  have hn1 : 2 * y / s < (n : ℝ) + 1 := Int.lt_floor_add_one _
  have hm0 : (m : ℝ) ≤ x - (n : ℝ) / 2 := Int.floor_le _
  have hm1 : x - (n : ℝ) / 2 < (m : ℝ) + 1 := Int.lt_floor_add_one _
  have hu0 : 0 ≤ u := by dsimp [u]; linarith
  have hu1 : u ≤ 1 := by dsimp [u]; linarith
  have hv0 : 0 ≤ v := by
    have h := (le_div_iff₀ hs).mp hn0
    dsimp [v]
    nlinarith
  have hv1 : v ≤ s / 2 := by
    have h := (div_lt_iff₀ hs).mp hn1
    dsimp [v]
    nlinarith
  rcases triangular_rectangle_cover s u v hs hsq hu0 hu1 hv0 hv1 with h | h | h
  · exact ⟨m, n, h⟩
  · refine ⟨m + 1, n, ?_⟩
    have hu : x - (((m + 1 : ℤ) : ℝ) + (n : ℝ) / 2) = u - 1 := by
      dsimp [u]
      push_cast
      ring
    rw [hu]
    exact h
  · refine ⟨m, n + 1, ?_⟩
    have hu : x - ((m : ℝ) + ((n + 1 : ℤ) : ℝ) / 2) = u - 1 / 2 := by
      dsimp [u]
      push_cast
      ring
    have hv : y - Real.sqrt 3 * ((n + 1 : ℤ) : ℝ) / 2 = v - s / 2 := by
      dsimp [v, s]
      push_cast
      ring
    rw [hu, hv]
    exact h
