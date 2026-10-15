-- Prove2me | solution 1 for OAI.TriangularCovering.d_le_max_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:01:06.717149+00:00
-- url     : https://prove2.me/submissions/9862c668-8e6d-4097-9287-03fec0d0bcbe

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CoordinateCover.lean:L19-L38
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.d_le_max_endpoints. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {a b q : ℝ} (ha : a ≤ q) (hb : q ≤ b) :
    d q ≤ max (d a) (d b) := by
  have hsq : q ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
    by_cases hq : 0 ≤ q
    · have hbb : 0 ≤ b := le_trans hq hb
      exact le_trans (sq_le_sq₀ hq hbb |>.mpr hb) (le_max_right _ _)
    · have hqa : a ≤ 0 := le_trans ha (le_of_not_ge hq)
      have hqa' : q ≤ 0 := le_of_not_ge hq
      have : q ^ 2 ≤ a ^ 2 := by nlinarith
      exact le_trans this (le_max_left _ _)
  rcases le_max_iff.mp hsq with h | h
  · apply le_trans _ (le_max_left _ _)
    dsimp [d]
    nlinarith [sq_nonneg (a ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg a,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]
  · apply le_trans _ (le_max_right _ _)
    dsimp [d]
    nlinarith [sq_nonneg (b ^ 2 - q ^ 2), sq_nonneg q, sq_nonneg b,
      mul_nonneg (sub_nonneg.mpr h) (sq_nonneg q)]
