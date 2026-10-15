-- Prove2me | solution 1 for OAI.RuledApproximation.singular_region_estimates
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:35:24.26766+00:00
-- url     : https://prove2.me/submissions/135a5016-64c2-4437-9eee-0f1bcdf2843b

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularOverlap.lean:L24-L95
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singular_region_estimates. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_RuledCovering
import Definitions.Def_OAI_Geometry_RuledCovering_Projection
import Definitions.Def_OAI_Geometry_RuledCovering_Frames
import Definitions.Def_OAI_Geometry_RuledCovering_OuterApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_Lattice
import Definitions.Def_OAI_Geometry_RuledCovering_LocalApproximation
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicLattice
import Definitions.Def_OAI_Geometry_RuledCovering_HyperbolicCover
import Definitions.Def_OAI_Geometry_RuledCovering_Isometries
import Definitions.Def_OAI_Geometry_RuledCovering_Hyperbolic
import Definitions.Def_OAI_Geometry_RuledCovering_NilpotentLattice
import Definitions.Def_OAI_Geometry_RuledCovering_Nilpotent
import Definitions.Def_OAI_Geometry_RuledCovering_SingularField
import Theorems.Thm_OAI_RuledApproximation_singularField_contDiffAt

-- ---- from OAI.Geometry.RuledCovering.SingularField ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularField_level (p b : ℝ) :
    singularField p (vec2 b (1/2)) = vec2 (p/4+(2-p)*b^2) b := by
  ext i
  fin_cases i <;> simp [singularField,vec2]; ring

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma plane_norm_sq (z : Plane) : ‖z‖^2 = z 0^2+z 1^2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg ‖z i‖))]
  simp [Fin.sum_univ_succ,Real.norm_eq_abs]

lemma plane_coordinate_le (z : Plane) (i : Fin 2) : |z i| ≤ ‖z‖ := by
  simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le z i

lemma plane_norm_le_sum (z : Plane) : ‖z‖ ≤ |z 0|+|z 1| := by
  have h := plane_norm_sq z
  have h0 := abs_nonneg (z 0)
  have h1 := abs_nonneg (z 1)
  nlinarith [sq_abs (z 0),sq_abs (z 1)]

end RuledApproximation

end

end OAI

-- ---- from OAI.Geometry.RuledCovering.SingularOverlap ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singular_region_estimates (p : ℝ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ (z : Plane) (B : ℝ),
      |z 0| ≤ 2 → (1/2:ℝ) ≤ z 1 → z 1 ≤ 2 → |B| ≤ 2 →
      |singularField p z 0| ≤ K ∧
      |singularField p z 1-z 0| ≤ K*(z 1-1/2) ∧
      |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*(|z 0-B|+(z 1-1/2)) ∧
      |ceilingPolynomial p (z 0)-ceilingPolynomial p B| ≤ K*|z 0-B| := by
  let S : Set Plane := (EuclideanSpace.proj 0) ⁻¹' Icc (-2:ℝ) 2 ∩
    (EuclideanSpace.proj 1) ⁻¹' Icc (1/2:ℝ) 2
  have hSc : IsClosed S := (isClosed_Icc.preimage (by fun_prop)).inter
    (isClosed_Icc.preimage (by fun_prop))
  have hS : IsCompact S := (isCompact_closedBall (0:Plane) 4).of_isClosed_subset hSc (by
    intro z hz
    change z 0 ∈ Icc (-2:ℝ) 2 ∧ z 1 ∈ Icc (1/2:ℝ) 2 at hz
    rw [Metric.mem_closedBall,dist_zero_right]
    have ha : |z 0| ≤ 2 := abs_le.mpr hz.1
    have hb : |z 1| ≤ 2 := (abs_of_nonneg (by linarith [hz.2.1])).le.trans hz.2.2
    exact (plane_norm_le_sum z).trans (by linarith))
  have hconv : Convex ℝ S := ((convex_Icc (-2:ℝ) 2).linear_preimage (EuclideanSpace.proj 0).toLinearMap).inter
    ((convex_Icc (1/2:ℝ) 2).linear_preimage (EuclideanSpace.proj 1).toLinearMap)
  have hsmooth : ∀ z ∈ S, ContDiffAt ℝ ∞ (singularField p) z := by
    intro z hz
    apply singularField_contDiffAt
    have hz1 : (1/2:ℝ) ≤ z 1 := hz.2.1
    linarith
  obtain ⟨C₀,hC₀⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (hsmooth z hz).continuousAt.continuousWithinAt)
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((hsmooth z hz).continuousAt_fderiv (by norm_num)).continuousWithinAt)
  have hdelta : ContDiff ℝ ∞ (ceilingPolynomial p) := by unfold ceilingPolynomial; fun_prop
  obtain ⟨C₂,hC₂⟩ := (isCompact_Icc (a := (-2:ℝ)) (b := 2)).exists_bound_of_continuousOn
    (f := fderiv ℝ (ceilingPolynomial p))
    (fun _ _ => (hdelta.contDiffAt.continuousAt_fderiv (by norm_num)).continuousWithinAt)
  let K := max 1 (max C₀ (max C₁ C₂))
  have hK : 1 ≤ K := le_max_left _ _
  have hK₀ : C₀ ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hK₁ : C₁ ≤ K := (le_max_left _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hK₂ : C₂ ≤ K := (le_max_right _ _).trans
    ((le_max_right _ _).trans (le_max_right _ _))
  have hKn : 0 ≤ K := by linarith
  have hlip : ∀ z ∈ S, ∀ w ∈ S, ‖singularField p z-singularField p w‖ ≤ K*‖z-w‖ := by
    intro z hz w hw
    exact Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun q hq => (hsmooth q hq).differentiableAt (by norm_num))
      (fun q hq => (hC₁ q hq).trans hK₁) hconv hw hz
  have hdlip : ∀ b ∈ Icc (-2:ℝ) 2, ∀ B ∈ Icc (-2:ℝ) 2,
      |ceilingPolynomial p b-ceilingPolynomial p B| ≤ K*|b-B| := by
    intro b hb B hB
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_fderiv_le
      (f := ceilingPolynomial p) (fun _ _ => hdelta.differentiable (by norm_num) _)
      (fun q hq => (hC₂ q hq).trans hK₂) (convex_Icc _ _) hB hb
  refine ⟨K,hK,?_⟩
  intro z B hz0 hz1 hz2 hB
  have hz : z ∈ S := ⟨abs_le.mp hz0,⟨hz1,hz2⟩⟩
  have hw : vec2 (z 0) (1/2) ∈ S := ⟨abs_le.mp hz0,by norm_num [vec2]⟩
  have hwB : vec2 B (1/2) ∈ S := ⟨abs_le.mp hB,by norm_num [vec2]⟩
  refine ⟨(plane_coordinate_le _ 0).trans ((hC₀ z hz).trans hK₀),?_,?_,hdlip _ (abs_le.mp hz0) _ (abs_le.mp hB)⟩
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 (z 0) (1/2))) 1).trans (hlip z hz _ hw)
    rw [singularField_level] at h
    change |singularField p z 1-z 0| ≤ K*‖z-vec2 (z 0) (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 (z 0) (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,sub_self,abs_zero,zero_add,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn
  · have h := (plane_coordinate_le (singularField p z-singularField p (vec2 B (1/2))) 0).trans (hlip z hz _ hwB)
    rw [singularField_level] at h
    change |singularField p z 0-(p/4+(2-p)*B^2)| ≤ K*‖z-vec2 B (1/2)‖ at h
    apply h.trans
    have he := plane_norm_le_sum (z-vec2 B (1/2))
    simpa only [PiLp.sub_apply,vec2_apply_zero,vec2_apply_one,
      abs_of_nonneg (sub_nonneg.mpr hz1)] using mul_le_mul_of_nonneg_left he hKn

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singular_region_estimates := @_root_.OAI.RuledApproximation.singular_region_estimates
