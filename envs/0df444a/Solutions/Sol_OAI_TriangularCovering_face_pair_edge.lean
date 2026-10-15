-- Prove2me | solution 1 for OAI.TriangularCovering.face_pair_edge
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:23:03.876958+00:00
-- url     : https://prove2.me/submissions/81354308-c5d0-4219-9b4c-d7ba0de683f0

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Shadows.lean:L147-L194
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.face_pair_edge. Inline helpers are the
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

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Shadows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

end TriangularCovering

namespace TriangularCovering

lemma vertical_edge_mem (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    point ((1-t)*a) (t*b) t ∈ triangle (point a 0 0) (point 0 b 1) (point 0 b 1) := by
  rw [mem_triangle_iff]
  refine ⟨t,0,ht0,le_rfl,by linarith,?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma upper_edge_mem (y : ℝ) (hy : |y| ≤ 1) :
    point 0 y 1 ∈ triangle (point 0 (-1) 1) (point 0 1 1) (point 0 1 1) := by
  rw [mem_triangle_iff]
  refine ⟨(y+1)/2,0,by linarith [(abs_le.mp hy).1],le_rfl,
    by linarith [(abs_le.mp hy).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma lower_edge_mem (x : ℝ) (hx : |x| ≤ 1) :
    point x 0 0 ∈ triangle (point (-1) 0 0) (point 1 0 0) (point 1 0 0) := by
  rw [mem_triangle_iff]
  refine ⟨(x+1)/2,0,by linarith [(abs_le.mp hx).1],le_rfl,
    by linarith [(abs_le.mp hx).2],?_⟩
  ext i
  fin_cases i <;> dsimp [point] <;> ring

lemma face_coord (i : Fin 4) (x y t : ℝ) :
    inner ℝ (faceNormal i) (point x y t) = faceBound i ↔
      (![x+t,-x+t,y-t,-y-t] : Fin 4 → ℝ) i = (![1,1,0,0] : Fin 4 → ℝ) i := by
  fin_cases i <;> simp only [inner_coord] <;> dsimp [faceNormal,faceBound,point]
  all_goals constructor <;> intro h <;> nlinarith only [H_pos,h]

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {i j : Fin 4} (hij : i ≠ j) :
    ∃ a b : Space, face i ∩ face j ⊆ triangle a b b := by
  wlog hlt : i < j generalizing i j
  · obtain ⟨a,b,hab⟩ := this hij.symm (lt_of_le_of_ne (le_of_not_gt hlt) hij.symm)
    exact ⟨a,b,by simpa only [inter_comm] using hab⟩
  fin_cases i <;> fin_cases j <;> norm_num at hlt
  · refine ⟨point 0 (-1) 1,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 1 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 1 := by linarith only [hi',hj']
    have hx0 : x = 0 := by linarith only [hi',hj']
    subst t; subst x
    exact upper_edge_mem y hy
  · refine ⟨point 1 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point 1 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 0 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem 1 (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 1 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 2 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) 1 t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 0 (-1) 1,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 1 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    convert vertical_edge_mem (-1) (-1) t ht0 ht1 using 1; congr 1 <;> linarith only [hi',hj']
  · refine ⟨point (-1) 0 0,point 1 0 0,?_⟩
    rintro z ⟨⟨⟨x,y,t,ht0,ht1,hx,hy,rfl⟩,hi⟩,_,hj⟩
    have hi' := (face_coord 2 x y t).mp hi
    have hj' := (face_coord 3 x y t).mp hj
    dsimp at hi' hj'
    have ht : t = 0 := by linarith only [hi',hj']
    have hy0 : y = 0 := by linarith only [hi',hj']
    subst t; subst y
    exact lower_edge_mem x (by simpa using hx)
