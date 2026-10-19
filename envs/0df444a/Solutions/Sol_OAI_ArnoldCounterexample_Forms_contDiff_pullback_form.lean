-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.contDiff_pullback_form
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:22:28.380538+00:00
-- url     : https://prove2.me/submissions/fb03dea0-1cd7-4ce0-a512-942f9ea96aaa

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Homotopy.lean:L114-L138
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.contDiff_pullback_form. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_ArnoldCounterexample
import Definitions.Def_OAI_Geometry_Arnold_Involution
import Definitions.Def_OAI_Geometry_Arnold_Projective
import Definitions.Def_OAI_Geometry_Arnold_Rotation
import Definitions.Def_OAI_Geometry_Arnold_Tangent
import Definitions.Def_OAI_Geometry_Arnold_Haar
import Definitions.Def_OAI_Geometry_Arnold_Differentiation
import Definitions.Def_OAI_Geometry_Arnold_Orbit
import Definitions.Def_OAI_Geometry_Arnold_Symplectic
import Definitions.Def_OAI_Geometry_Arnold_Coordinates
import Definitions.Def_OAI_Geometry_Arnold_Extension
import Definitions.Def_OAI_Geometry_Arnold_Deformation
import Definitions.Def_OAI_Geometry_Arnold_Exterior
import Definitions.Def_OAI_Geometry_Arnold_Homotopy

-- ---- from OAI.Geometry.Arnold.Homotopy ----
namespace OAI

universe uE uD uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Smoothness into finite-dimensional alternating forms can be checked after
forgetting alternation. This uses an honest linear retraction, not an axiom. -/
lemma contDiff_of_toMultilinear {D : Type uD} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [FiniteDimensional ℝ E] {n : ℕ} {k : ℕ∞ω}
    {f : D → E [⋀^Fin n]→L[ℝ] ℝ}
    (hf : ContDiff ℝ k (fun x ↦ (f x).toContinuousMultilinearMap)) : ContDiff ℝ k f := by
  let L := (toContinuousMultilinearMapCLM (𝕜 := ℝ) (E := E) (F := ℝ) (ι := Fin n) ℝ).toLinearMap
  have hL : LinearMap.ker L = ⊥ := LinearMap.ker_eq_bot.mpr toContinuousMultilinearMap_injective
  obtain ⟨R, hR⟩ := L.exists_leftInverse_of_injective hL
  have heq : f = fun x ↦ R.toContinuousLinearMap ((f x).toContinuousMultilinearMap) := by
    funext x
    exact (LinearMap.congr_fun hR (f x)).symm
  rw [heq]
  exact R.toContinuousLinearMap.contDiff.comp hf

lemma contDiff_pullback_form {D : Type uD} {F : Type uF}
    [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ E] {n : ℕ} {k : ℕ∞ω}
    {θ : D → F [⋀^Fin n]→L[ℝ] ℝ} {L : D → E →L[ℝ] F}
    (hθ : ContDiff ℝ k θ) (hL : ContDiff ℝ k L) :
    ContDiff ℝ k (fun x ↦ (θ x).compContinuousLinearMap (L x)) := by
  apply contDiff_of_toMultilinear
  let : TopologicalSpace (E →L[ℝ] F) :=
    (inferInstance : NormedAddCommGroup (E →L[ℝ] F)).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let : TopologicalSpace ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (inferInstance : NormedAddCommGroup ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ))).toMetricSpace.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace
  let P : ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E →L[ℝ] F)
      ((F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) :=
    (ContinuousMultilinearMap.compContinuousLinearMapMultilinear
      ℝ (fun _ : Fin n ↦ E) (fun _ ↦ F) ℝ).mkContinuous 1 (by
        intro g
        rw [one_mul]
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le ℝ g)
  have hPc : ContDiff ℝ k (fun g : Fin n → E →L[ℝ] F ↦ P g) := by
    exact ContinuousMultilinearMap.contDiff (𝕜 := ℝ)
      (E := fun _ : Fin n ↦ E →L[ℝ] F)
      (F := (F [×n]→L[ℝ] ℝ) →L[ℝ] (E [×n]→L[ℝ] ℝ)) P
  have hP := hPc.comp (contDiff_pi.mpr (fun _ ↦ hL))
  exact hP.clm_apply ((toContinuousMultilinearMapCLM (𝕜 := ℝ) (E := F) (F := ℝ) (ι := Fin n) ℝ).contDiff.comp hθ)

end ArnoldCounterexample.Forms

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.Forms
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function
open ContinuousAlternatingMap
open scoped BigOperators ContDiff
open ContinuousAlternatingMap


theorem solution.{uE,uD,uF} : type_of% @_root_.OAI.ArnoldCounterexample.Forms.contDiff_pullback_form.{uE,uD,uF} := @_root_.OAI.ArnoldCounterexample.Forms.contDiff_pullback_form.{uE,uD,uF}
