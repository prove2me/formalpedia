-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:19:11.97792+00:00
-- url     : https://prove2.me/submissions/264e6612-f485-4c1f-9a2a-6d391028c8e9

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Homotopy.lean:L51-L88
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity. The node keeps its source
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

/-- The time derivative of a closed form restricted to slices is the spatial
exterior derivative of its contraction with the time direction. -/
theorem cylinder_homotopy_identity {n : ℕ}
    (Θ : ℝ × E → (ℝ × E) [⋀^Fin (n + 1)]→L[ℝ] ℝ)
    (hΘ : Differentiable ℝ Θ) (t : ℝ) (z : E)
    (hclosed : extDeriv Θ (t, z) = 0) (v : Fin (n + 1) → E) :
    extDeriv (sliceContraction Θ t) z v =
      (fderiv ℝ Θ (t, z) (1, 0)) (fun i ↦ (0, v i)) := by
  have hr {k : ℕ} (i : Fin (k + 1)) (w : Fin (k + 1) → ℝ × E) :
      i.succ.removeNth (Matrix.vecCons (1, 0) w) =
        Matrix.vecCons (1, 0) (i.removeNth w) :=
    Fin.cons_comp_succ_succAbove (1, 0) w i
  have hd : fderiv ℝ (sliceContraction Θ t) z =
      (cylinderContraction n).comp ((fderiv ℝ Θ (t, z)).comp spatial) := by
    exact ((cylinderContraction n).hasFDerivAt.comp z
      ((hΘ (t, z)).hasFDerivAt.comp z
        ((hasFDerivAt_const (c := t) z).prodMk (hasFDerivAt_id z)))).fderiv
  have hc : extDeriv Θ (t, z) (Matrix.vecCons (1, 0) (fun i ↦ (0, v i))) = 0 := by
    rw [hclosed]; rfl
  simp only [extDeriv, alternatizeUncurryFin_apply] at hc ⊢
  rw [Fin.sum_univ_succ] at hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.removeNth_zero,
    Fin.val_zero, pow_zero, one_smul, hr, Fin.val_succ, pow_succ,
    mul_neg_one, neg_smul, Finset.sum_neg_distrib] at hc
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, spatial_apply, cylinderContraction_apply]
  have heq : (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (fun j ↦ (0, (i.removeNth v) j)))) =
      (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (i.removeNth (fun j ↦ (0, v j))))) := rfl
  rw [heq]
  change (fderiv ℝ Θ (t, z) (1, 0)) (fun i ↦ (0, v i)) -
    (∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val •
      (fderiv ℝ Θ (t, z) (0, v i))
        (Matrix.vecCons (1, 0) (i.removeNth (fun j ↦ (0, v j))))) = 0 at hc
  linarith

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


theorem solution.{uE} : type_of% @_root_.OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity.{uE} := @_root_.OAI.ArnoldCounterexample.Forms.cylinder_homotopy_identity.{uE}
