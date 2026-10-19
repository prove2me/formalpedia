-- Prove2me | solution 1 for OAI.ArnoldCounterexample.Forms.cubeForm_radical_on
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T10:17:10.715389+00:00
-- url     : https://prove2.me/submissions/06251d34-c56a-4f5b-bd05-182666d003d2

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Exterior.lean:L100-L122
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.Forms.cubeForm_radical_on. The node keeps its source
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
import Theorems.Thm_OAI_ArnoldCounterexample_Forms_pairForm_radical

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

lemma pairForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (B : F →L[ℝ] F →L[ℝ] ℝ) (η : F [⋀^Fin n]→L[ℝ] ℝ)
    (L : E →L[ℝ] F) (v : Fin (n + 2) → E) :
    pairForm B η (L ∘ v) =
      pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) v := by
  simp only [pairForm_apply, ContinuousLinearMap.bilinearComp_apply,
    compContinuousLinearMap_apply, Function.comp_apply]
  rfl

lemma cubeForm_pullback {F : Type uF} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (B : F →L[ℝ] F →L[ℝ] ℝ) (L : E →L[ℝ] F) :
    (cubeForm B).compContinuousLinearMap L = cubeForm (B.bilinearComp L L) := by
  have hpair {n : ℕ} (η : F [⋀^Fin n]→L[ℝ] ℝ) :
      (pairForm B η).compContinuousLinearMap L =
        pairForm (B.bilinearComp L L) (η.compContinuousLinearMap L) := by
    ext v
    exact pairForm_pullback B η L v
  simp only [cubeForm, squareForm, hpair]
  congr 3

lemma cubeForm_radical (B : E →L[ℝ] E →L[ℝ] ℝ)
    (u : E) (hl : ∀ v, B u v = 0) (hr : ∀ v, B v u = 0)
    (v : Fin 5 → E) : cubeForm B (Matrix.vecCons u v) = 0 := by
  apply pairForm_radical B (squareForm B) u hl hr
  intro w
  apply pairForm_radical B _ u hl hr
  intro w
  simp [pairForm_apply, Fin.sum_univ_succ, Fin.removeNth, hl, hr]

/-- The third symplectic power vanishes when one input lies in the radical
of the bilinear form on the span of all six inputs. -/
lemma cubeForm_radical_on (B : E →L[ℝ] E →L[ℝ] ℝ)
    (hskew : ∀ u v, B u v = - B v u) (u : E) (v : Fin 5 → E)
    (horth : ∀ i, B u (v i) = 0) : cubeForm B (Matrix.vecCons u v) = 0 := by
  let S := (B u).ker
  have hu : u ∈ S := by
    change B u u = 0
    linarith [hskew u u]
  let u' : S := ⟨u, hu⟩
  let v' : Fin 5 → S := fun i ↦ ⟨v i, horth i⟩
  let B' := B.bilinearComp S.subtypeL S.subtypeL
  have hl (w : S) : B' u' w = 0 := w.property
  have hr (w : S) : B' w u' = 0 := by
    change B w u = 0
    rw [hskew]
    exact neg_eq_zero.mpr w.property
  have hzero := cubeForm_radical B' u' hl hr v'
  rw [← cubeForm_pullback B S.subtypeL] at hzero
  have heq : S.subtypeL ∘ Matrix.vecCons u' v' = Matrix.vecCons u v := by
    funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i <;> rfl
  simpa only [compContinuousLinearMap_apply, heq] using hzero

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


theorem solution.{uE} : type_of% @_root_.OAI.ArnoldCounterexample.Forms.cubeForm_radical_on.{uE} := @_root_.OAI.ArnoldCounterexample.Forms.cubeForm_radical_on.{uE}
