-- Prove2me | solution 1 for OAI.TriangularCovering.main
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-14T23:57:00.759091+00:00
-- url     : https://prove2.me/submissions/a793bd6a-7f57-4188-bff0-5360b16e3092

-- Generated from openai/math@1581d4c lean/OAI/Geometry/TriangularCovering/Main.lean:L60-L62
-- (upload_full_project.md Phase 4): solution for the platform mission target OAI.TriangularCovering.main.
-- The statement is the platform stub (Theorems.Thm_OAI_TriangularCovering_main) verbatim; the proof is the source proof;
-- inline helpers are the source spans of the proof-only lemmas it needs.
import Mathlib
import Definitions.Def_TriangularCovering
import Definitions.Def_OAI_Geometry_TriangularCovering_CoordinateCover
import Definitions.Def_OAI_Geometry_TriangularCovering_TriangleArea
import Definitions.Def_OAI_Geometry_TriangularCovering_Projection
import Definitions.Def_OAI_Geometry_TriangularCovering_CylinderFamily
import Definitions.Def_OAI_Geometry_TriangularCovering_Tetrahedron
import Definitions.Def_OAI_Geometry_TriangularCovering_Shadows
import Definitions.Def_OAI_Geometry_TriangularCovering_Asymptotics
import Theorems.Thm_OAI_TriangularCovering_finiteFamily_total
import Theorems.Thm_OAI_TriangularCovering_finite_coordinate_cover
import Theorems.Thm_OAI_TriangularCovering_sector_weights
import Theorems.Thm_OAI_TriangularCovering_shadowArea_formula
import Theorems.Thm_OAI_TriangularCovering_shadowArea_ge_H
import Theorems.Thm_OAI_TriangularCovering_uniform_scalar_sum

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CoordinateCover ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

theorem ceil_step_le {ε : ℝ} (he : 0 < ε) : step ⌈2 / ε ^ 2⌉₊ ≤ ε ^ 2 := by
  have hn := ceil_count_pos he
  have hn' : (0 : ℝ) < ⌈2 / ε ^ 2⌉₊ := by exact_mod_cast hn
  unfold step
  rw [div_le_comm₀ hn' (sq_pos_of_pos he)]
  exact Nat.le_ceil _

/-- Coverage with the exact ceiling count, in intercept coordinates. -/
theorem finite_coordinate_cover_ceil {ε x y t : ℝ}
    (he0 : 0 < ε) (he1 : ε ≤ η / 2) (hx : |x| ≤ 1 - t) (hy : |y| ≤ t) :
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ LowerHit ⌈2 / ε ^ 2⌉₊ j ε x y t) ∨
    (∃ j : ℕ, j < ⌈2 / ε ^ 2⌉₊ ∧ UpperHit ⌈2 / ε ^ 2⌉₊ j ε x y t) :=
  finite_coordinate_cover (ceil_count_pos he0) he0 he1 (ceil_step_le he0) hx hy

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

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

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Projection ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma projectedCylinder_mem (u : Space) (hu : ‖u‖ = 1) (a b c : Space)
    (h : inner ℝ u (cross3 (b-a) (c-a)) ≠ 0) {p z : Space} (hp : p ∈ triangle a b c)
    (r : ℝ) (hz : z = p + r • u) : z ∈ (projectedCylinder u hu a b c h).carrier := by
  refine ⟨projection u p, ⟨p, hp, rfl⟩, r + inner ℝ u p, ?_⟩
  change z = projection u p + (r + inner ℝ u p) • u
  rw [hz, projection]
  module

lemma unit_mul_norm (v : Space) : ‖v‖ • unit v = v := by
  by_cases hv : v = 0
  · simp [unit, hv]
  · simp [unit, smul_smul, norm_ne_zero_iff.mpr hv]

lemma projectedCylinder_mem_direction (v : Space) (hv : v ≠ 0) (a b c : Space)
    (h : inner ℝ (unit v) (cross3 (b-a) (c-a)) ≠ 0) {p z : Space}
    (hp : p ∈ triangle a b c) (r : ℝ) (hz : z = p + r • v) :
    z ∈ (projectedCylinder (unit v) (unit_norm hv) a b c h).carrier := by
  apply projectedCylinder_mem (unit v) (unit_norm hv) a b c h hp (r * ‖v‖)
  rw [mul_smul, unit_mul_norm, hz]

end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.CylinderFamily ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma H_sq : H^2 = 2 := by norm_num [H]

lemma tiltV_norm (ε A B : ℝ) : ‖tiltV ε A B‖ = Real.sqrt (1+ε^2*(A^2+2*B^2)) := by
  rw [← Real.sqrt_sq (norm_nonneg _), ← real_inner_self_eq_norm_sq, inner_coord]
  dsimp [tiltV]
  congr 1
  nlinarith only [H_sq]

lemma lower_triangle_mem {a b T y t : ℝ} (hab : a < b) (hT : 0 < T)
    (ht0 : 0 ≤ t) (htT : t ≤ T) (hay : a*t ≤ y) (hyb : y ≤ b*t) :
    point 0 y t ∈ triangle (lowerVertices a b T 0)
      (lowerVertices a b T 1) (lowerVertices a b T 2) := by
  obtain ⟨r,s,hr,hs,hrs,het,hey⟩ := sector_weights hab hT ht0 htT hay hyb
  rw [mem_triangle_iff]
  refine ⟨r,s,hr,hs,hrs,?_⟩
  ext i
  fin_cases i <;> dsimp [lowerVertices, point]
  · ring
  · nlinarith only [hey]
  · linear_combination -H * het

lemma upper_triangle_mem {a b T x s : ℝ} (hab : a < b) (hT : 0 < T)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) (hax : a*s ≤ x) (hxb : x ≤ b*s) :
    point x 0 (1-s) ∈ triangle (upperVertices a b T 0)
      (upperVertices a b T 1) (upperVertices a b T 2) := by
  obtain ⟨r,q,hr,hq,hrq,hes,hex⟩ := sector_weights hab hT hs0 hsT hax hxb
  rw [mem_triangle_iff]
  refine ⟨r,q,hr,hq,hrq,?_⟩
  ext i
  fin_cases i <;> dsimp [upperVertices, point]
  · nlinarith only [hex]
  · ring
  · linear_combination H * hes

lemma lowerCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hr0 : 0 ≤ t-ε*x*B) (hrT : t-ε*x*B ≤ T)
    (hl : a*(t-ε*x*B) ≤ y-ε*x*A) (hu : y-ε*x*A ≤ b*(t-ε*x*B)) :
    point x y t ∈ (lowerCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltV ε A B) (tiltV_ne_zero ε A B)
    _ _ _ _ (lower_triangle_mem hab hT hr0 hrT hl hu) x
  ext i
  fin_cases i <;> dsimp [point, tiltV] <;> ring

lemma upperCylinder_hit {a b T : ℝ} (hab : a < b) (hT : 0 < T) (ε A B x y t : ℝ)
    (hs0 : 0 ≤ 1-t+ε*y*B) (hsT : 1-t+ε*y*B ≤ T)
    (hl : a*(1-t+ε*y*B) ≤ x+ε*y*A) (hu : x+ε*y*A ≤ b*(1-t+ε*y*B)) :
    point x y t ∈ (upperCylinder hab hT ε A B).carrier := by
  apply projectedCylinder_mem_direction (tiltW ε A B) (tiltW_ne_zero ε A B)
    _ _ _ _ (upper_triangle_mem hab hT hs0 hsT hl hu) y
  ext i
  fin_cases i <;> dsimp [point, tiltW] <;> ring

end TriangularCovering

namespace TriangularCovering

lemma finiteFamily_covers {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) :
    Covers (finiteFamily ε he) := by
  rintro z ⟨x,y,t,_ht0,_ht1,hx,hy,rfl⟩
  rcases finite_coordinate_cover_ceil he hsmall hx hy with ⟨j,hj,hl⟩ | ⟨j,hj,hu⟩
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.castAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_left]
    exact lowerCylinder_hit _ _ _ _ _ _ _ _ hl.1.1 hl.2 hl.1.2.1 hl.1.2.2
  · refine ⟨Fin.cast (two_mul (n ε)).symm (Fin.natAdd (n ε) (⟨j,hj⟩ : Fin (n ε))), ?_⟩
    simp only [finiteFamily, Function.comp_apply, Fin.cast_cast, Fin.cast_eq_self,
      Fin.append_right]
    exact upperCylinder_hit _ _ _ _ _ _ _ _ hu.1.1 hu.2 hu.1.2.1 hu.1.2.2

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

end TriangularCovering

namespace TriangularCovering

lemma xAxis_unit : ‖tiltV 0 0 0‖ = 1 := by rw [tiltV_norm]; norm_num

lemma xAxis_shadow : shadowArea (tiltV 0 0 0) = H := by
  rw [shadowArea_formula xAxis_unit]
  dsimp [tiltV]
  simp [H_pos.le]

/-- The minimum Euclidean shadow area equals the height H. -/
theorem projection_minimum : A_min = H := by
  unfold A_min
  apply le_antisymm
  · apply csInf_le
    · exact ⟨H,by rintro a ⟨u,hu,rfl⟩; exact shadowArea_ge_H hu⟩
    · exact ⟨tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
  · apply le_csInf
    · exact ⟨H,tiltV 0 0 0,xAxis_unit,xAxis_shadow.symm⟩
    · rintro a ⟨u,hu,rfl⟩
      exact shadowArea_ge_H hu

end TriangularCovering

namespace TriangularCovering

end TriangularCovering

end

end OAI

-- ---- inline helpers from OAI.Geometry.TriangularCovering.Main ----
namespace OAI

open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

noncomputable section
namespace TriangularCovering

lemma small_abs_le_one {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) : |ε| ≤ 1 := by
  rw [abs_of_pos he]
  dsimp [η] at hsmall
  linarith only [hsmall]

/-- The area expansion with explicit uniform remainder constant 14. -/
theorem finiteFamily_expansion {ε : ℝ} (he : 0 < ε) (hsmall : ε ≤ η/2) :
    |totalArea (finiteFamily ε he)/H - (1/2-(13/6000:ℝ)*ε^2)| ≤ 14*ε^4 := by
  rw [finiteFamily_total]
  exact uniform_scalar_sum (small_abs_le_one he hsmall) (ceil_count_pos he) (ceil_step_le he)

lemma finiteFamily_ratio_lt {ε : ℝ} (he : 0 < ε) (hsmall : ε < η/2) :
    totalArea (finiteFamily ε he)/H < 1/2 := by
  have hr := (abs_le.mp (finiteFamily_expansion he hsmall.le)).2
  have hesq : ε^2 < (η/2)^2 := (sq_lt_sq₀ he.le (by norm_num [η])).2 hsmall
  have hc : 14*ε^2 < (13/6000:ℝ) := by norm_num [η] at hesq; linarith only [hesq]
  have hneg := mul_neg_of_pos_of_neg (sq_pos_of_pos he) (sub_neg.mpr hc)
  nlinarith only [hr,hneg]

lemma finiteFamily_strict {ε : ℝ} (he : 0 < ε) (hsmall : ε < η/2) :
    totalArea (finiteFamily ε he) < A_min/2 := by
  rw [projection_minimum]
  have h := (div_lt_iff₀ H_pos).mp (finiteFamily_ratio_lt he hsmall)
  linarith only [h]

/-- The asymptotic covering bound, including exact finite count and strict saving. -/
theorem main_asymptotic : MainAsymptotic := by
  refine ⟨η/2,14,by norm_num [η],by norm_num,?_⟩
  intro ε he hsmall
  exact ⟨finiteFamily ε he,finiteFamily_covers he hsmall.le,
    finiteFamily_expansion he hsmall.le,finiteFamily_strict he hsmall⟩

lemma relativeCost_le_totalArea {m : ℕ} (c : Fin m → TriCylinder) :
    relativeCost c ≤ totalArea c/H := by
  unfold relativeCost totalArea
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro i _
  exact div_le_div_of_nonneg_left ENNReal.toReal_nonneg H_pos
    (shadowArea_ge_H (c i).unit_axis)

/-- The normalized covering bound using perpendicular shadows. -/
theorem normalized_counterexample : NormalizedCounterexample := by
  have he : 0 < η/4 := by norm_num [η]
  have hs : η/4 < η/2 := by norm_num [η]
  refine ⟨2*n (η/4),finiteFamily (η/4) he,finiteFamily_covers he hs.le,?_⟩
  exact (relativeCost_le_totalArea _).trans_lt (finiteFamily_ratio_lt he hs)

end TriangularCovering

end

end OAI

-- ---- hoisted mission target ----
open OAI OAI.TriangularCovering
open Set MeasureTheory
open scoped InnerProductSpace BigOperators Interval

theorem solution : A_min = H ∧ MainAsymptotic ∧ NormalizedCounterexample :=
  ⟨projection_minimum,main_asymptotic,normalized_counterexample⟩
