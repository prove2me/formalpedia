-- Prove2me | solution 1 for OAI.TriangularCovering.shadowArea_ge_H
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:26:36.856172+00:00
-- url     : https://prove2.me/submissions/268c984c-dd88-42fd-ac5d-af9782502522

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Shadows.lean:L276-L294
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.shadowArea_ge_H. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
import Theorems.Thm_OAI_TriangularCovering_shadowArea_formula

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CylinderFamily ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_sq : H^2 = 2 := by norm_num [H]

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {u : Space} (hu : ‖u‖ = 1) : H ≤ shadowArea u := by
  rw [shadowArea_formula hu]
  let A := max (H*|u 0|) |u 2|
  let B := max (H*|u 1|) |u 2|
  have hA : H*|u 0| ≤ A := le_max_left _ _
  have hB : H*|u 1| ≤ B := le_max_left _ _
  have hAz : |u 2| ≤ A := le_max_right _ _
  have hBz : |u 2| ≤ B := le_max_right _ _
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hAz
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hBz
  have hAs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 0))) hA 2
  have hBs := pow_le_pow_left₀ (mul_nonneg H_pos.le (abs_nonneg (u 1))) hB 2
  rw [mul_pow,H_sq,sq_abs] at hAs hBs
  have hAB := mul_le_mul hAz hBz (abs_nonneg _) hA0
  have hu2 := real_inner_self_eq_norm_sq u
  rw [inner_coord,hu] at hu2
  have hz2 : |u 2| * |u 2| = (u 2)^2 := by nlinarith only [sq_abs (u 2)]
  change H ≤ A+B
  nlinarith only [hu2,hAs,hBs,hAB,hz2,H_sq,H_pos,hA0,hB0]
