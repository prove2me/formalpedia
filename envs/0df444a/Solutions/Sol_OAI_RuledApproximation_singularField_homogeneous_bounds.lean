-- Prove2me | solution 1 for OAI.RuledApproximation.singularField_homogeneous_bounds
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:28:59.359367+00:00
-- url     : https://prove2.me/submissions/43c0a64f-86df-4ee7-afa7-a41b60d10ae2

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/SingularBounds.lean:L25-L67
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.singularField_homogeneous_bounds. The node keeps its source
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
import Theorems.Thm_OAI_RuledApproximation_singularField_fderiv_smul
import Theorems.Thm_OAI_RuledApproximation_singularField_smul

-- ---- from OAI.Geometry.RuledCovering.SingularBounds ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

lemma singularField_homogeneous_bounds (p : ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ z : Plane, 0 < z 1 → |z 0| ≤ 2*z 1 →
      ‖singularField p z‖ ≤ C*(z 1)^(p-1) ∧
      ‖fderiv ℝ (singularField p) z‖ ≤ C*(z 1)^(p-2) := by
  let S : Set Plane := (fun b : ℝ => vec2 b 1) '' Icc (-2 : ℝ) 2
  have hS : IsCompact S := isCompact_Icc.image (by unfold vec2; fun_prop)
  have hpos : ∀ z ∈ S, 0 < z 1 := by
    rintro z ⟨b,hb,rfl⟩
    norm_num [vec2]
  obtain ⟨C₁,hC₁⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => (singularField_contDiffAt p (hpos z hz)).continuousAt.continuousWithinAt)
  obtain ⟨C₂,hC₂⟩ := hS.exists_bound_of_continuousOn
    (fun z hz => ((singularField_contDiffAt p (hpos z hz)).continuousAt_fderiv
      (by norm_num)).continuousWithinAt)
  refine ⟨max 1 (max C₁ C₂),le_max_left _ _,?_⟩
  intro z hz hcone
  let u := vec2 (z 0/z 1) 1
  have hu : u ∈ S := by
    refine ⟨z 0/z 1,?_,rfl⟩
    have ht : |z 0/z 1| ≤ 2 := by
      rw [abs_div,abs_of_pos hz,div_le_iff₀ hz]
      exact hcone
    exact abs_le.mp ht
  have hue : z 1 • u = z := by
    ext i
    fin_cases i <;> simp [u,vec2]
    field_simp
  have hf := singularField_smul p hz (z := u) (by norm_num [u,vec2])
  have hd := singularField_fderiv_smul p hz (z := u) (by norm_num [u,vec2])
  rw [hue] at hf hd
  constructor
  · rw [hf,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-1)*C₁ := mul_le_mul_of_nonneg_left (hC₁ u hu) (by positivity)
      _ ≤ (z 1)^(p-1)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_left _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _
  · rw [hd,norm_smul,Real.norm_eq_abs,abs_of_pos (Real.rpow_pos_of_pos hz _)]
    calc
      _ ≤ (z 1)^(p-2)*C₂ := mul_le_mul_of_nonneg_left (hC₂ u hu) (by positivity)
      _ ≤ (z 1)^(p-2)*max 1 (max C₁ C₂) := mul_le_mul_of_nonneg_left
        ((le_max_right _ _).trans (le_max_right _ _)) (by positivity)
      _ = _ := mul_comm _ _

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.singularField_homogeneous_bounds := @_root_.OAI.RuledApproximation.singularField_homogeneous_bounds
