-- Prove2me | solution 2 for OAI.ProjectionMoments.rotation_transitive
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T19:23:51.097842+00:00
-- url     : https://prove2.me/submissions/c396d313-e69f-44aa-a129-86bb9563753e

-- Generated from openai/math@1581d4c lean/OAI/Probability/ProjectionMoments/Frames.lean:L44-L68
-- (upload_full_project.md Phase 4): solution for node OAI.ProjectionMoments.rotation_transitive. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Gram__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Projection__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Support__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Blocks__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Sphere__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Stream__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Caps__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Execution__ProjectionMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Rotational__ProjectionMoments
import Definitions.Def_OAI_Probability_ProjectionMoments_Graph
import Definitions.Def_OAI_Probability_ProjectionMoments_Frames

-- ---- from OAI.Probability.ProjectionMoments.Frames ----
-- Lean 4.34 name, proved using the Mathlib 0df444a lemma (same statement); as in oai-math-oct-2026.
namespace OAI

open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology
noncomputable section
namespace ProjectionMoments
attribute [fun_prop] measurable_lowerDensity

section Rotations
variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

variable {E}

lemma rotation_transitive {ι : Type*} [Fintype ι] {u v : ι → E}
    (hu : Orthonormal ℝ u) (hv : Orthonormal ℝ v) :
    ∃ O : Rotation E, ∀ i, (O : E →L[ℝ] E) (u i) = v i := by
  classical
  let U := Submodule.span ℝ (Set.range u)
  let V := Submodule.span ℝ (Set.range v)
  let bu : OrthonormalBasis ι ℝ U := (Module.Basis.span hu.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hu using 1; ext i; simp)
  let bv : OrthonormalBasis ι ℝ V := (Module.Basis.span hv.linearIndependent).toOrthonormalBasis
    (by convert! orthonormal_span hv using 1; ext i; simp)
  let e : U ≃ₗᵢ[ℝ] V := bu.repr.trans bv.repr.symm
  let L : U →ₗᵢ[ℝ] E := V.subtypeₗᵢ.comp e.toLinearIsometry
  let O : E ≃ₗᵢ[ℝ] E := L.extend.toLinearIsometryEquiv rfl
  refine ⟨Unitary.linearIsometryEquiv.symm O, ?_⟩
  intro i
  change O (u i) = v i
  change L.extend (u i) = v i
  have he : e (bu i) = bv i := by
    simp only [e, LinearIsometryEquiv.trans_apply, OrthonormalBasis.repr_self,
      OrthonormalBasis.repr_symm_single]
  have hbui : (bu i : E) = u i := by simp [bu, Module.Basis.span_apply]
  have hbvi : (bv i : E) = v i := by simp [bv, Module.Basis.span_apply]
  rw [← hbui, LinearIsometry.extend_apply]
  change (e (bu i) : E) = _
  rw [he, hbvi]

variable [MeasurableSpace E] [BorelSpace E]

end Rotations

section Triangular
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end Triangular

section CoordinateDensity
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

end CoordinateDensity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

end ProjectionMoments
end

end OAI

-- ---- platform node ----
open OAI OAI.ProjectionMoments
open MeasureTheory ProbabilityTheory Set Filter InnerProductSpace
open scoped ENNReal NNReal RealInnerProductSpace Topology


theorem solution : type_of% @_root_.OAI.ProjectionMoments.rotation_transitive := @_root_.OAI.ProjectionMoments.rotation_transitive
