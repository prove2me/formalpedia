-- Prove2me | solution 1 for OAI.TriangularCovering.shadowArea_formula
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T19:24:57.030715+00:00
-- url     : https://prove2.me/submissions/1e92cdbf-2a75-4ead-bc55-f58d09152993

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Shadows.lean:L254-L274
-- (upload_full_project.md Phase 4): solution for node OAI.TriangularCovering.shadowArea_formula. Inline helpers are the
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
import Theorems.Thm_OAI_TriangularCovering_K_halfspaces
import Theorems.Thm_OAI_TriangularCovering_face_eq_triangle
import Theorems.Thm_OAI_TriangularCovering_face_pair_edge

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Tetrahedron ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma face_cross (i : Fin 4) :
    cross3 (faceVertices i 1-faceVertices i 0) (faceVertices i 2-faceVertices i 0) =
      (![2,-2,2,-2] : Fin 4 → ℝ) i • faceNormal i := by
  fin_cases i <;> ext k <;> fin_cases k <;>
    dsimp [cross3,faceVertices,faceNormal,point,crossProduct] <;> ring

lemma face_projection_measure {u : Space} (hu : ‖u‖ = 1) (i : Fin 4) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' face i) =
      ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [face_eq_triangle, projection_triangle_measure hu, face_cross,
    inner_smul_right, real_inner_comm u (faceNormal i), abs_mul]
  have hh : |(![2,-2,2,-2] : Fin 4 → ℝ) i| = 2 := by fin_cases i <;> norm_num
  rw [hh]
  congr 1
  ring

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Shadows ----
-- Lean 4.33.1 equivalents of the upstream Lean 4.34 theorem names.
private theorem ite_eq_left.{u} {c : Prop} {h : Decidable c} (hc : c) {α : Sort u} {t e : α} : (ite c t e) = t := @if_pos c h hc α t e
private theorem ite_eq_right.{u} {c : Prop} {h : Decidable c} (hc : ¬c) {α : Sort u} {t e : α} : (ite c t e) = e := @if_neg c h hc α t e

namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma faceNormal_sum (u : Space) : ∑ i : Fin 4, inner ℝ (faceNormal i) u = 0 := by
  simp only [Fin.sum_univ_succ, inner_coord]
  dsimp [faceNormal]
  ring

lemma positive_face_exists {u : Space} (hu : ‖u‖ = 1) :
    ∃ i : Fin 4, 0 < inner ℝ (faceNormal i) u := by
  by_contra h
  push Not at h
  have h0 := h 0; have h1 := h 1; have h2 := h 2; have h3 := h 3
  simp only [inner_coord] at h0 h1 h2 h3
  dsimp [faceNormal] at h0 h1 h2 h3
  have hz : u 2 = 0 := by linarith only [h0,h1,h2,h3]
  have hx : u 0 = 0 := by nlinarith only [h0,h1,hz,H_pos]
  have hy : u 1 = 0 := by nlinarith only [h2,h3,hz,H_pos]
  have hun : u = 0 := by ext i; fin_cases i <;> assumption
  simp [hun] at hu

lemma projection_add_axis {u : Space} (hu : ‖u‖ = 1) (z : Space) (r : ℝ) :
    projection u (z+r•u) = projection u z := by
  simp only [projection, inner_add_right, inner_smul_right, real_inner_self_eq_norm_sq,hu]
  module

lemma forward_face {u : Space} (hu : ‖u‖ = 1) {z : Space} (hz : z ∈ K) :
    ∃ i ∈ front u, ∃ p ∈ face i, projection u p = projection u z := by
  classical
  have hfront : (front u).Nonempty := by
    obtain ⟨i,hi⟩ := positive_face_exists hu
    exact ⟨i,(mem_front u i).mpr hi⟩
  obtain ⟨i,hi,hmin⟩ := Finset.exists_min_image (front u)
    (fun i => (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u) hfront
  let r := (faceBound i-inner ℝ (faceNormal i) z)/inner ℝ (faceNormal i) u
  have hi0 : 0 < inner ℝ (faceNormal i) u := (mem_front u i).mp hi
  have hzi := K_halfspaces z |>.mp hz
  have hr : 0 ≤ r := div_nonneg (sub_nonneg.mpr (hzi i)) hi0.le
  have hre : r * inner ℝ (faceNormal i) u = faceBound i-inner ℝ (faceNormal i) z := by
    dsimp [r]
    exact div_mul_cancel₀ _ (ne_of_gt hi0)
  refine ⟨i,hi,z+r•u,⟨?_,?_⟩,projection_add_axis hu z r⟩
  · rw [K_halfspaces]
    intro j
    simp only [inner_add_right,inner_smul_right]
    by_cases hj : 0 < inner ℝ (faceNormal j) u
    · have hm := hmin j ((mem_front u j).mpr hj)
      have hm' : r * inner ℝ (faceNormal j) u ≤ faceBound j-inner ℝ (faceNormal j) z :=
        (le_div_iff₀ hj).mp hm
      linarith only [hm']
    · have hn := mul_nonpos_of_nonneg_of_nonpos hr (le_of_not_gt hj)
      linarith only [hn,hzi j]
  · rw [inner_add_right,inner_smul_right,hre]
    ring

lemma shadow_front {u : Space} (hu : ‖u‖ = 1) :
    projection u '' K = ⋃ i ∈ front u, projection u '' face i := by
  ext q
  constructor
  · rintro ⟨z,hz,rfl⟩
    obtain ⟨i,hi,p,hp,hpq⟩ := forward_face hu hz
    exact mem_iUnion.mpr ⟨i,mem_iUnion.mpr ⟨hi,⟨p,hp,hpq⟩⟩⟩
  · intro h
    obtain ⟨i,hi,p,hp,hpq⟩ := mem_iUnion.mp h |>.imp (fun _ => mem_iUnion.mp)
    exact ⟨p,hp.1,hpq⟩

lemma projected_faces_inter_subset {u : Space} {i j : Fin 4}
    (hi : i ∈ front u) (hj : j ∈ front u) :
    (projection u '' face i) ∩ (projection u '' face j) ⊆ projection u '' (face i ∩ face j) := by
  rintro q ⟨⟨p,hp,hpq⟩,⟨z,hz,hzq⟩⟩
  have hh : projection u p = projection u z := hpq.trans hzq.symm
  let r := inner ℝ u p - inner ℝ u z
  have hpe : p = z+r•u := by
    dsimp [projection] at hh
    dsimp [r]
    calc
      p = (p-inner ℝ u p•u)+inner ℝ u p•u := by abel
      _ = (z-inner ℝ u z•u)+inner ℝ u p•u := by rw [hh]
      _ = z+(inner ℝ u p-inner ℝ u z)•u := by module
  have hzi := (K_halfspaces z).mp hz.1 i
  have hpj := (K_halfspaces p).mp hp.1 j
  have he_i : inner ℝ (faceNormal i) p =
      inner ℝ (faceNormal i) z+r*inner ℝ (faceNormal i) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have he_j : inner ℝ (faceNormal j) p =
      inner ℝ (faceNormal j) z+r*inner ℝ (faceNormal j) u := by
    rw [hpe,inner_add_right,inner_smul_right]
  have hr0 : 0 ≤ r := by
    have := (mem_front u i).mp hi
    nlinarith only [hzi,hp.2,he_i,this]
  have hr1 : r ≤ 0 := by
    have := (mem_front u j).mp hj
    nlinarith only [hpj,hz.2,he_j,this]
  have hr : r = 0 := le_antisymm hr1 hr0
  have hpz : p = z := by simpa [hr] using hpe
  exact ⟨p,⟨hp,hpz.symm ▸ hz⟩,hpq⟩

end TriangularCovering

namespace TriangularCovering

lemma cross3_self (a : Space) : cross3 a a = 0 := by
  rw [cross3_coord]
  ext i
  fin_cases i <;> dsimp <;> ring

lemma face_pair_projection_null {u : Space} (hu : ‖u‖ = 1) {i j : Fin 4} (hij : i ≠ j) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' (face i ∩ face j)) = 0 := by
  obtain ⟨a,b,hab⟩ := face_pair_edge hij
  apply measure_mono_null (image_mono hab)
  rw [projection_triangle_measure hu, cross3_self,inner_zero_right,abs_zero,zero_div,ENNReal.ofReal_zero]

lemma front_pairwise_aeDisjoint {u : Space} (hu : ‖u‖ = 1) :
    (↑(front u) : Set (Fin 4)).Pairwise
      (fun i j => AEDisjoint (Measure.euclideanHausdorffMeasure 2)
        (projection u '' face i) (projection u '' face j)) := by
  intro i hi j hj hij
  exact measure_mono_null (projected_faces_inter_subset hi hj) (face_pair_projection_null hu hij)

lemma shadow_measure {u : Space} (hu : ‖u‖ = 1) :
    Measure.euclideanHausdorffMeasure 2 (projection u '' K) =
      ∑ i ∈ front u, ENNReal.ofReal |inner ℝ (faceNormal i) u| := by
  rw [shadow_front hu,measure_biUnion_finset₀ (front_pairwise_aeDisjoint hu)]
  · exact Finset.sum_congr rfl (fun i _ => face_projection_measure hu i)
  · intro i _hi
    rw [face_eq_triangle]
    exact ((triangle_compact _ _ _).image
      (projLinear u).continuous_of_finiteDimensional).measurableSet.nullMeasurableSet

end TriangularCovering

namespace TriangularCovering

lemma max_pos_abs (a : ℝ) : max a 0 = (|a|+a)/2 := by
  by_cases h : 0 ≤ a
  · rw [max_eq_left h,abs_of_nonneg h]; ring
  · rw [max_eq_right (le_of_not_ge h),abs_of_nonpos (le_of_not_ge h)]; ring

lemma shadowArea_positive_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = ∑ i : Fin 4, max (inner ℝ (faceNormal i) u) 0 := by
  rw [shadowArea,area,shadow_measure hu,ENNReal.toReal_sum (fun _ _ => ENNReal.ofReal_ne_top)]
  simp only [ENNReal.toReal_ofReal (abs_nonneg _)]
  rw [front,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : 0 < inner ℝ (faceNormal i) u
  · rw [ite_eq_left h,abs_of_pos h,max_eq_left h.le]
  · rw [ite_eq_right h,max_eq_right (le_of_not_gt h)]

lemma shadowArea_abs_sum {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = (∑ i : Fin 4, |inner ℝ (faceNormal i) u|)/2 := by
  rw [shadowArea_positive_sum hu]
  simp_rw [max_pos_abs]
  rw [← Finset.sum_div,Finset.sum_add_distrib,faceNormal_sum,add_zero]

lemma abs_pair (a b : ℝ) : |a+b|+|a-b| = 2*max |a| |b| := by
  simp only [abs_eq_max_neg,max_def]
  split_ifs <;> linarith

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- hoisted node ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution {u : Space} (hu : ‖u‖ = 1) :
    shadowArea u = max (H*|u 0|) |u 2| + max (H*|u 1|) |u 2| := by
  rw [shadowArea_abs_sum hu,Fin.sum_univ_four]
  simp only [inner_coord]
  dsimp [faceNormal]
  have h1 := abs_pair (H*u 0) (u 2)
  have h2 := abs_pair (H*u 1) (u 2)
  rw [abs_mul,abs_of_pos H_pos] at h1 h2
  have he1 : |-H*u 0+0*u 1+1*u 2| = |H*u 0-u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  have he2 : |0*u 0+-H*u 1+-1*u 2| = |H*u 1+u 2| := by
    rw [← abs_neg]
    congr 1
    ring
  rw [he1,he2]
  have he3 : |H*u 0+0*u 1+1*u 2| = |H*u 0+u 2| := by congr 1; ring
  have he4 : |0*u 0+H*u 1+-1*u 2| = |H*u 1-u 2| := by congr 1; ring
  rw [he3,he4]
  linarith only [h1,h2]
