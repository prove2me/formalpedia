-- Prove2me | solution 1 for OAI.TriangularCovering.inv_sqrt_remainder
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:28:36.182121+00:00
-- url     : https://prove2.me/submissions/effabcaa-9069-41cd-950e-b76848a99149

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Asymptotics.lean:L11-L34
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.inv_sqrt_remainder. Inline helpers are the
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
import Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {x : ℝ} (hx : 0 ≤ x) :
    |1 / Real.sqrt (1+x) - (1-x/2)| ≤ x^2 := by
  let t := Real.sqrt (1+x)
  have ht : 1 ≤ t := by
    dsimp [t]
    exact (Real.le_sqrt (by norm_num) (by linarith)).2 (by linarith)
  have ht0 : 0 < t := lt_of_lt_of_le zero_lt_one ht
  have ht2 : t^2 = 1+x := Real.sq_sqrt (by linarith)
  have hden : 0 < 2*t*(t+1)^2 := by positivity
  have hfac : 0 ≤ (t+2)/(2*t*(t+1)^2) := by positivity
  have hfac1 : (t+2)/(2*t*(t+1)^2) ≤ 1 := by
    apply (div_le_one hden).2
    have hs : 4 ≤ (t+1)^2 := by nlinarith only [ht]
    have hp := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*t)
    nlinarith only [hp,ht]
  have heq : 1/t-(1-x/2) = x^2*((t+2)/(2*t*(t+1)^2)) := by
    have hxid : x=t^2-1 := by linarith only [ht2]
    rw [hxid]
    field_simp
    ring
  change |1/t-(1-x/2)| ≤ x^2
  rw [heq,abs_of_nonneg (mul_nonneg (sq_nonneg x) hfac)]
  exact mul_le_of_le_one_right (sq_nonneg x) hfac1
