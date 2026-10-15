-- Prove2me | solution 1 for OAI.TriangularCovering.sector_weights
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:15:51.13591+00:00
-- url     : https://prove2.me/submissions/2e58b247-5a54-44d6-b5ab-54fce53cb9ab

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/CylinderFamily.lean:L106-L122
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.sector_weights. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (_ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ r*T+s*T=t ∧ r*(a*T)+s*(b*T)=y := by
  let r := (b*t-y)/((b-a)*T)
  let s := (y-a*t)/((b-a)*T)
  have hden : 0 < (b-a)*T := mul_pos (sub_pos.mpr hab) hT
  have hrs : r*T+s*T = t := by
    dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr hyb) hden.le
  have hs : 0 ≤ s := div_nonneg (sub_nonneg.mpr hay) hden.le
  refine ⟨r,s,hr,hs,?_,hrs,?_⟩
  · nlinarith only [hrs, htT, hT]
  · dsimp [r,s]
    field_simp [ne_of_gt (sub_pos.mpr hab), ne_of_gt hT]
    ring
