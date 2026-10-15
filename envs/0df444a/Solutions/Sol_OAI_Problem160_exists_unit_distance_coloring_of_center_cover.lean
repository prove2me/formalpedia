-- Prove2me | solution 1 for OAI.Problem160.exists_unit_distance_coloring_of_center_cover
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T17:42:08.632795+00:00
-- url     : https://prove2.me/submissions/caabca5d-740f-4f79-bdd6-75bf61f61b04

-- Generated from openai/math@1581d4c lean/OAI/Geometry/PlaneColoring/Assembly.lean:L9-L37
-- (upload_full_project.md Phase 4): solution for node OAI.Problem160.exists_unit_distance_coloring_of_center_cover. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_PlaneColoring

-- ---- hoisted node ----
open OAI OAI.Problem160

theorem solution
    {X I : Type*} [PseudoMetricSpace X] {k : ℕ}
    (center : I → X) (color : I → Fin k) (r : ℝ)
    (hcover : ∀ x : X, ∃ i : I, dist x (center i) ≤ r)
    (hdiam : 2 * r < 1)
    (hsep : ∀ i j : I, i ≠ j → color i = color j →
      1 + 2 * r < dist (center i) (center j)) :
    ∃ c : X → Fin k, ∀ x y : X, dist x y = 1 → c x ≠ c y := by
  classical
  choose cell hcell using hcover
  refine ⟨fun x => color (cell x), ?_⟩
  intro x y hdist hcolor
  by_cases hsame : cell x = cell y
  · have htriangle := dist_triangle x (center (cell x)) y
    have hx := hcell x
    have hy := hcell y
    rw [← hsame] at hy
    rw [dist_comm (center (cell x)) y] at htriangle
    linarith
  · have hfar := hsep (cell x) (cell y) hsame hcolor
    have htriangle₁ := dist_triangle (center (cell x)) x (center (cell y))
    have htriangle₂ := dist_triangle x y (center (cell y))
    have hx := hcell x
    have hy := hcell y
    rw [dist_comm (center (cell x)) x] at htriangle₁
    linarith
