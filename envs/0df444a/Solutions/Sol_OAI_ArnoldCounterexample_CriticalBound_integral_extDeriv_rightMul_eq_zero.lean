-- Prove2me | solution 1 for OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-19T09:53:21.947559+00:00
-- url     : https://prove2.me/submissions/204d10a4-87a6-4870-9518-2d666b48296c

-- Generated from openai/math@1581d4c lean/OAI/Geometry/Arnold/Differentiation.lean:L68-L102
-- (upload_full_project.md Phase 4): solution for node OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero. The node keeps its source
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
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_contDiff_multilinear_apply
import Theorems.Thm_OAI_ArnoldCounterexample_CriticalBound_integral_fderiv_mul_skew_eq_zero

-- ---- from OAI.Geometry.Arnold.Differentiation ----
namespace OAI

universe uE uF uG

noncomputable section
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator

namespace ArnoldCounterexample.CriticalBound

theorem contDiff_alternating_apply {E : Type uE} {F : Type uF} {G : Type uG}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {k : ℕ∞ω} {n : ℕ} {f : E → F [⋀^Fin n]→L[ℝ] G}
    (hf : ContDiff ℝ k f) {v : Fin n → E → F} (hv : ∀ i, ContDiff ℝ k (v i)) :
    ContDiff ℝ k (fun x ↦ f x (v · x)) := by
  convert! contDiff_multilinear_apply ((ContinuousAlternatingMap.toContinuousMultilinearMapCLM ℝ).contDiff.comp hf) hv using 1

end ArnoldCounterexample.CriticalBound

namespace ArnoldCounterexample.CriticalBound
open VectorField

lemma fderiv_rightMul (X A B : RM) :
    fderiv ℝ (fun Y : RM ↦ Y * X) A B = B * X := by
  have h := ((hasFDerivAt_id (𝕜 := ℝ) A).mul_const' X).fderiv
  convert! congrArg (fun f : RM →L[ℝ] RM ↦ f B) h using 1

lemma lieBracket_rightMul (X Y A : RM) :
    lieBracket ℝ (fun B : RM ↦ B * X) (fun B : RM ↦ B * Y) A =
      A * (X * Y - Y * X) := by
  dsimp only [lieBracket]
  convert! congrArg₂ (fun P Q : RM ↦ P - Q) (fderiv_rightMul Y A (A * X))
    (fderiv_rightMul X A (A * Y)) using 1
  simp only [mul_sub, mul_assoc]

/-- Haar--Stokes on horizontal tuples of left-invariant fields. The bracket
hypothesis is basicness in the vertical directions; it is purely a pointwise
algebraic condition, not a Stokes or nonexactness assumption. -/
theorem integral_extDeriv_rightMul_eq_zero {n : ℕ}
    (W : RM → MatForm (n + 1)) (hW : ContDiff ℝ ∞ W)
    (X : Fin (n + 2) → RM) (hX : ∀ i, star (X i) = -X i)
    (hvertical : ∀ (A : O5) (i j : Fin (n + 1)),
      W A (Matrix.vecCons ((A : RM) * (X i.castSucc * X j.succ - X j.succ * X i.castSucc))
        (j.removeNth (i.castSucc.removeNth (fun k ↦ (A : RM) * X k)))) = 0) :
    ∫ A : O5, extDeriv W (A : RM) (fun i ↦ (A : RM) * X i) ∂haar = 0 := by
  let F : Fin (n + 2) → RM → ℝ := fun i A ↦ W A (i.removeNth (fun k ↦ A * X k))
  have hF (i : Fin (n + 2)) : ContDiff ℝ ∞ (F i) := by
    exact contDiff_alternating_apply hW (fun _ ↦ contDiff_id.mul contDiff_const)
  have hpoint (A : O5) : extDeriv W (A : RM) (fun i ↦ (A : RM) * X i) =
      ∑ i, (-1 : ℝ) ^ i.val * fderiv ℝ (F i) (A : RM) ((A : RM) * X i) := by
    have h := extDeriv_apply_vectorField (V := fun i (A : RM) ↦ A * X i)
      (hW.differentiable (by simp) (A : RM))
      (fun i ↦ (contDiff_id.mul (contDiff_const (c := X i)) : ContDiff ℝ ∞ _).differentiable (by simp) _)
    convert! h.trans ?_ using 1
    simp only [lieBracket_rightMul, hvertical, smul_zero, Finset.sum_const_zero, sub_zero]
    simp only [← Int.cast_smul_eq_zsmul ℝ, Int.cast_pow, Int.cast_neg, Int.cast_one, smul_eq_mul]
    congr! 2
  simp_rw [hpoint]
  rw [integral_finsetSum]
  · apply Finset.sum_eq_zero
    intro i _
    rw [integral_const_mul]
    have hi := integral_fderiv_mul_skew_eq_zero (F i) (hF i) (X i) (hX i)
    convert! congrArg ((-1 : ℝ) ^ i.val * ·) hi using 1
    simp only [mul_zero]
  · intro i _
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact continuous_const.mul
      (((hF i).continuous_fderiv (by simp)).comp continuous_subtype_val |>.clm_apply
        (continuous_subtype_val.mul continuous_const))

end ArnoldCounterexample.CriticalBound

end

end OAI

-- ---- platform node ----
open OAI OAI.ArnoldCounterexample OAI.ArnoldCounterexample.CriticalBound
open scoped BigOperators ContDiff
open MeasureTheory Set Filter
open scoped Matrix.Norms.Operator
open VectorField


theorem solution : type_of% @_root_.OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero := @_root_.OAI.ArnoldCounterexample.CriticalBound.integral_extDeriv_rightMul_eq_zero
