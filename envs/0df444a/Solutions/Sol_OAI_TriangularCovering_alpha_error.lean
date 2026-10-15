-- Prove2me | solution 1 for OAI.TriangularCovering.alpha_error
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:03:44.611036+00:00
-- url     : https://prove2.me/submissions/4e09c33f-ef9d-426c-82ee-2a1bea3842b6

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L99-L113
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.alpha_error. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {a b q : ℝ} (ha : |a| ≤ 1) (hq : |q| ≤ 1)
    (haq : a ≤ q) (hqb : q ≤ b) :
    |alpha a b - (1 + q ^ 2) / 4| ≤ (b - a) / 2 := by
  have e : alpha a b - (1 + q ^ 2) / 4 = (a * (b - q) + q * (a - q)) / 4 := by
    dsimp [alpha]; ring
  rw [e, abs_div]
  norm_num
  have h1 : |a * (b - q)| ≤ b - q := by
    rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hqb)]
    exact mul_le_of_le_one_left (sub_nonneg.mpr hqb) ha
  have h2 : |q * (a - q)| ≤ q - a := by
    rw [abs_mul, abs_of_nonpos (sub_nonpos.mpr haq)]
    nlinarith [mul_le_of_le_one_left (sub_nonneg.mpr haq) hq]
  have h3 := abs_add_le (a * (b - q)) (q * (a - q))
  linarith
