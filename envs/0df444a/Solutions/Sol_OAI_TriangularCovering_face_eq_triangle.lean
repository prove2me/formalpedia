-- Prove2me | solution 1 for OAI.TriangularCovering.face_eq_triangle
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:21:11.682774+00:00
-- url     : https://prove2.me/submissions/c6c196ab-da1c-4049-83a0-d14b3d8bd825

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Tetrahedron.lean:L63-L106
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.face_eq_triangle. Inline helpers are the
-- source spans of proof-only lemmas this proof needs; the node is hoisted out of its namespace
-- as a top-level `theorem solution` with the namespace re-opened.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Theorems.Thm_OAI_TriangularCovering_K_halfspaces

-- ---- inline helpers from OAI.Geometry.TriangularCovering.TriangleArea ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering.Planar

end TriangularCovering.Planar

namespace TriangularCovering

section Triangles
variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]

lemma mem_triangle_iff (a b c x : E) : x ∈ triangle a b c ↔
    ∃ r s : ℝ, 0 ≤ r ∧ 0 ≤ s ∧ r+s ≤ 1 ∧ x = a + r • (b-a) + s • (c-a) := by
  rw [triangle_translate, triangle_zero_image]
  constructor
  · rintro ⟨y, ⟨v, hv, rfl⟩, rfl⟩
    exact ⟨v 0, v 1, hv.1, hv.2.1, hv.2.2, by simp [add_assoc]⟩
  · rintro ⟨r, s, hr, hs, hrs, rfl⟩
    refine ⟨r • (b-a) + s • (c-a), ?_, by simp [add_assoc]⟩
    exact ⟨![r,s], ⟨hr, hs, hrs⟩, by simp⟩

end Triangles

namespace Planar

end Planar
end TriangularCovering

namespace TriangularCovering

section InnerPlane
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

end InnerPlane
end TriangularCovering

namespace TriangularCovering

section SubspaceMeasure
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

end SubspaceMeasure
end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Tetrahedron ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma K_convex : Convex ℝ K := by
  have : K = ⋂ i, {z | inner ℝ (faceNormal i) z ≤ faceBound i} := by
    ext z
    simp only [mem_iInter, mem_ofPred_eq, K_halfspaces]
  rw [this]
  exact convex_iInter (fun i => convex_halfSpace_le (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

lemma face_vertices_mem (i : Fin 4) (j : Fin 3) : faceVertices i j ∈ face i := by
  refine ⟨?_,?_⟩
  · rw [K_halfspaces]
    intro k
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;>
      nlinarith only [H_pos]
  · fin_cases i <;> fin_cases j <;>
      simp only [inner_coord] <;> dsimp [faceVertices,faceNormal,faceBound,point] <;> ring

lemma face_convex (i : Fin 4) : Convex ℝ (face i) :=
  K_convex.inter (convex_hyperplane (innerₛₗ ℝ (faceNormal i)).isLinear (faceBound i))

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution (i : Fin 4) :
    face i = triangle (faceVertices i 0) (faceVertices i 1) (faceVertices i 2) := by
  apply Subset.antisymm
  · rintro z ⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hz⟩
    have hx' := abs_le.mp hx
    have hy' := abs_le.mp hy
    rw [mem_triangle_iff]
    fin_cases i
    · have hh : x = 1-t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : x = t-1 := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(t+y)/2,(t-y)/2,by linarith only [hy'.1],by linarith only [hy'.2],
        by linarith only [ht1],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
    · have hh : y = -t := by
        simp only [inner_coord] at hz
        dsimp [faceNormal,faceBound,point] at hz
        nlinarith only [hz,H_pos]
      refine ⟨(1-t+x)/2,(1-t-x)/2,by linarith only [hx'.1],by linarith only [hx'.2],
        by linarith only [ht0],?_⟩
      ext k
      fin_cases k <;> dsimp [faceVertices,point] <;> nlinarith only [hh]
  · apply convexHull_min
    · rintro z ⟨j,rfl⟩
      fin_cases j <;> exact face_vertices_mem i _
    · exact face_convex i
