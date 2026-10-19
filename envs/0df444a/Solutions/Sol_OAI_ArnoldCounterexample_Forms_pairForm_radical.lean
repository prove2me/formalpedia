-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.pairForm_radical
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:15:41.959716+00:00
-- url     : https://prove2.me/submissions/2b338ceb-06f9-4a41-be1e-08e398911134

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Exterior.lean:L37-L63
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.pairForm_radical. The node keeps its source
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

-- ---- from OAI.Geometry.Arnold.Exterior ----
namespace OAI

universe uE uF

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open scoped Topology
open Function

open scoped BigOperators ContDiff
open ContinuousAlternatingMap

namespace ArnoldCounterexample.Forms

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma pairForm_apply {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin n]→L[ℝ] ℝ) (v : Fin (n + 2) → E) :
    pairForm B η v = ∑ i : Fin (n + 2), ∑ j : Fin (n + 1),
      (-1 : ℝ) ^ i.val * (-1 : ℝ) ^ j.val *
        B (v i) ((i.removeNth v) j) * η (j.removeNth (i.removeNth v)) := by
  simp [pairForm, alternatizeUncurryFin_apply, ContinuousLinearMap.smulRightL,
    ← Int.cast_smul_eq_zsmul ℝ,
    smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- If all contractions of each factor vanish in a direction, so does their
alternating product. Restricting to the unit-sphere tangent gives basicness. -/
lemma pairForm_radical {n : ℕ} (B : E →L[ℝ] E →L[ℝ] ℝ)
    (η : E [⋀^Fin (n + 1)]→L[ℝ] ℝ) (u : E)
    (hleft : ∀ v, B u v = 0) (hright : ∀ v, B v u = 0)
    (hη : ∀ v : Fin n → E, η (Matrix.vecCons u v) = 0)
    (v : Fin (n + 2) → E) :
    pairForm B η (Matrix.vecCons u v) = 0 := by
  have hr {k : ℕ} (i : Fin (k + 1)) (v : Fin (k + 1) → E) :
      i.succ.removeNth (Matrix.vecCons u v) = Matrix.vecCons u (i.removeNth v) :=
    Fin.cons_comp_succ_succAbove u v i
  rw [pairForm_apply, Fin.sum_univ_succ]
  have hzero : (∑ j : Fin (n + 2),
      (-1 : ℝ) ^ (0 : Fin (n + 3)).val * (-1 : ℝ) ^ j.val *
      B (Matrix.vecCons u v 0) ((0 : Fin (n + 3)).removeNth (Matrix.vecCons u v) j) *
      η (j.removeNth ((0 : Fin (n + 3)).removeNth (Matrix.vecCons u v)))) = 0 := by
    simp [hleft]
  rw [hzero, zero_add]
  apply Finset.sum_eq_zero
  intro i _
  rw [Fin.sum_univ_succ]
  simp only [hr, Matrix.cons_val_succ, Matrix.cons_val_zero, hright,
    mul_zero, zero_mul, zero_add]
  apply Finset.sum_eq_zero
  intro j _
  rw [hη]
  exact mul_zero _

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
open scoped BigOperators ContDiff
open ContinuousAlternatingMap


theorem solution.{uE} : type_of% @_root_.OAI.ArnoldCounterexample.Forms.pairForm_radical.{uE} := @_root_.OAI.ArnoldCounterexample.Forms.pairForm_radical.{uE}
