-- Prove2me | solution 1 for OAI.RuledApproximation.nilpotent_frame
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-15T08:09:20.235023+00:00
-- url     : https://prove2.me/submissions/b204fffc-19eb-4fc8-ab70-9c8d306ff4f5

-- Generated from openai/math@1581d4c lean/OAI/Geometry/RuledCovering/NilpotentLattice.lean:L12-L77
-- (upload_full_project.md Phase 4): solution for node OAI.RuledApproximation.nilpotent_frame. The node keeps its source
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

-- ---- from OAI.Geometry.RuledCovering.NilpotentLattice ----
namespace OAI

noncomputable section

open Set MeasureTheory Filter Metric
open scoped Topology ContDiff Pointwise

namespace RuledApproximation

/-- A square-zero planar operator has an orthonormal shear frame, with no bound
on the shear coefficient. -/
lemma nilpotent_frame (A : Plane →L[ℝ] Plane) (hA : A.comp A = 0) :
    ∃ R : Plane ≃ₗᵢ[ℝ] Plane, ∃ d : ℝ, ∀ z : Plane,
      R.symm (A (R z)) = vec2 (d * z 1) 0 := by
  classical
  have hAA (x : Plane) : A (A x) = 0 := by
    have hh := congrArg (fun T : Plane →L[ℝ] Plane => T x) hA
    exact hh
  have hex : ∃ u : Plane, ‖u‖ = 1 ∧ A u = 0 := by
    by_cases hz : A = 0
    · refine ⟨vec2 1 0, ?_, by simp [hz]⟩
      simp [vec2, EuclideanSpace.norm_eq]
    · have hx : ∃ x : Plane, A x ≠ 0 := by
        by_contra h
        push Not at h
        apply hz
        apply ContinuousLinearMap.ext
        exact h
      obtain ⟨x, hx⟩ := hx
      refine ⟨‖A x‖⁻¹ • A x, ?_, ?_⟩
      · rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)]
      · simp [hAA]
  obtain ⟨u, hu, hAu⟩ := hex
  have hon : Orthonormal ℝ (({0} : Set (Fin 2)).domRestrict (fun _ => u)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hi : i = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp i.property)
    have hj : j = ⟨0, by simp⟩ := Subtype.ext (mem_singleton_iff.mp j.property)
    subst i
    subst j
    simp [hu]
  obtain ⟨b, hb⟩ := hon.exists_orthonormalBasis_extension_of_card_eq (by simp)
  let R : Plane ≃ₗᵢ[ℝ] Plane := b.repr.symm
  have hb0 : b 0 = u := hb 0 (by simp)
  have hrepr0 : b.repr (A (b 0)) = 0 := by rw [hb0, hAu, map_zero]
  let W : Plane →ₗ[ℝ] Plane := b.repr.toLinearMap.comp (A.toLinearMap.comp b.repr.symm.toLinearMap)
  have he0 : vec2 1 0 = EuclideanSpace.single 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hW0 : W (vec2 1 0) = 0 := by
    change b.repr (A (b.repr.symm (vec2 1 0))) = 0
    rw [he0, b.repr_symm_single]
    exact hrepr0
  have hWW (z : Plane) : W (W z) = 0 := by
    simp [W, hAA]
  have hexp (z : Plane) : z = z 0 • vec2 1 0 + z 1 • vec2 0 1 := by
    ext i
    fin_cases i <;> simp [vec2]
  have hWexp (z : Plane) : W z = z 1 • W (vec2 0 1) := by
    nth_rw 1 [hexp z]
    rw [map_add, map_smul, map_smul, hW0, smul_zero, zero_add]
  have hz11 : W (vec2 0 1) 1 = 0 := by
    have hs := congrArg (fun z : Plane => z 1) (hWW (vec2 0 1))
    rw [hWexp (W (vec2 0 1))] at hs
    change W (vec2 0 1) 1 * W (vec2 0 1) 1 = 0 at hs
    exact mul_self_eq_zero.mp hs
  refine ⟨R, W (vec2 0 1) 0, fun z => ?_⟩
  change W z = _
  rw [hWexp]
  ext i
  fin_cases i
  · change z 1 * W (vec2 0 1) 0 = W (vec2 0 1) 0 * z 1
    ring
  · change z 1 * W (vec2 0 1) 1 = 0
    rw [hz11, mul_zero]

end RuledApproximation

end

end OAI

-- ---- platform node ----
open OAI OAI.RuledApproximation
open Set MeasureTheory Filter Metric
open scoped Topology ContDiff


theorem solution : type_of% @_root_.OAI.RuledApproximation.nilpotent_frame := @_root_.OAI.RuledApproximation.nilpotent_frame
