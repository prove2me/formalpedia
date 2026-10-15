-- Prove2me | solution 1 for OAI.TriangularCovering.weighted_errors
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:08:30.93403+00:00
-- url     : https://prove2.me/submissions/6e7394fc-c923-4815-a1ef-13799b3d6cf7

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L190-L204
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.weighted_errors. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {ε Δ x y e f : ℝ} (he : 0 ≤ ε) (hΔ : 0 ≤ Δ)
    (hxy : |x| + |y| ≤ 1) (he' : |e| ≤ Δ / 4) (hf : |f| ≤ Δ / 4) :
    -ε * x * e + ε * y * f ≤ ε * Δ / 4 := by
  have h1 : -ε * x * e ≤ ε * |x| * (Δ / 4) := by
    calc
      -ε * x * e ≤ |-ε * x * e| := le_abs_self _
      _ = ε * |x| * |e| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |x| * (Δ / 4) := mul_le_mul_of_nonneg_left he' (by positivity)
  have h2 : ε * y * f ≤ ε * |y| * (Δ / 4) := by
    calc
      ε * y * f ≤ |ε * y * f| := le_abs_self _
      _ = ε * |y| * |f| := by simp [abs_mul, abs_of_nonneg he]
      _ ≤ ε * |y| * (Δ / 4) := mul_le_mul_of_nonneg_left hf (by positivity)
  have h3 := mul_le_mul_of_nonneg_right hxy (show 0 ≤ ε * Δ / 4 by positivity)
  nlinarith
