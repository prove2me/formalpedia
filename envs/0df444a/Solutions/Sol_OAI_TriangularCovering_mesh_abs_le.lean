-- Prove2me | solution 1 for OAI.TriangularCovering.mesh_abs_le
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:12:15.826047+00:00
-- url     : https://prove2.me/submissions/c2cdb2bd-ba91-4d09-8c03-05c4ec1bed9d

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L326-L338
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.mesh_abs_le. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {N j : ℕ} (hN : 0 < N) (hj : j ≤ N) : |mesh N j| ≤ 1 := by
  have h1 : 0 ≤ (j : ℝ) := Nat.cast_nonneg _
  have h2 : (j : ℝ) ≤ N := by exact_mod_cast hj
  have hstep := step_pos hN
  have hn : (N : ℝ) * step N = 2 := by
    have := mesh_last hN
    dsimp [mesh] at this
    linarith only [this]
  rw [abs_le]
  dsimp [mesh]
  constructor
  · nlinarith only [mul_nonneg h1 hstep.le]
  · nlinarith only [mul_le_mul_of_nonneg_right h2 hstep.le, hn]
