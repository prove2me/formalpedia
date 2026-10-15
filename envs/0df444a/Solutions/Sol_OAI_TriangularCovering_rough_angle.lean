-- Prove2me | solution 1 for OAI.TriangularCovering.rough_angle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:07:24.561423+00:00
-- url     : https://prove2.me/submissions/0c049edb-4ae3-4981-a28d-9982dc341058

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L131-L150
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.rough_angle. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {ε x y q a r : ℝ} (he : 0 ≤ ε)
    (hx : |x| ≤ 1) (hq : |q| ≤ 1) (ha : |a| ≤ 1 / 2)
    (hr0 : 1 / 2 ≤ r) (hr1 : r ≤ 1 / 2 + ε / 2)
    (hy : y = r * q + ε * x * a) : |y - q / 2| ≤ ε := by
  have heq : y - q / 2 = (r - 1 / 2) * q + ε * x * a := by rw [hy]; ring
  have h1 : |(r - 1 / 2) * q| ≤ ε / 2 := by
    rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ r - 1 / 2)]
    calc
      (r - 1 / 2) * |q| ≤ (r - 1 / 2) * 1 :=
        mul_le_mul_of_nonneg_left hq (by linarith)
      _ ≤ ε / 2 := by linarith
  have h2 : |ε * x * a| ≤ ε / 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg he]
    calc
      ε * |x| * |a| ≤ ε * 1 * (1 / 2) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hx he) ha (abs_nonneg _) (by positivity)
      _ = ε / 2 := by ring
  rw [heq]
  exact (abs_add_le _ _).trans (by linarith)
