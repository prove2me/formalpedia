-- Prove2me | solution 1 for OAI.TriangularCovering.K_halfspaces
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:19:14.312213+00:00
-- url     : https://prove2.me/submissions/6e527c4a-90f0-4fc4-926d-f4261485b71b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean:L25-L41
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.K_halfspaces. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Tetrahedron ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma point_coord (z : Space) : z = point (z 0) (z 1) (z 2/H) := by
  ext i
  fin_cases i <;> dsimp [point]
  field_simp [H_ne_zero]

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution (z : Space) : z ∈ K ↔ ∀ i, inner ℝ (faceNormal i) z ≤ faceBound i := by
  constructor
  · rintro ⟨x,y,t,ht0,ht1,hx,hy,rfl⟩ i
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point] <;>
      nlinarith only [H_pos, hx'.1, hx'.2, hy'.1, hy'.2]
  · intro h
    have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
    simp only [inner_coord] at h0 h1 h2 h3
    dsimp [faceNormal,faceBound] at h0 h1 h2 h3
    have ht : H * (z 2 / H) = z 2 := by field_simp [H_ne_zero]
    refine ⟨z 0,z 1,z 2/H,?_,?_,?_,?_,point_coord z⟩
    · nlinarith only [h2,h3,H_pos,ht]
    · nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h0,h1,H_pos,ht]
    · rw [abs_le]; constructor <;> nlinarith only [h2,h3,H_pos,ht]
