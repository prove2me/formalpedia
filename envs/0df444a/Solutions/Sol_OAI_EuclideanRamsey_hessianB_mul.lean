-- Prove2me | solution 1 for OAI.EuclideanRamsey.hessianB_mul
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:57:07.655378+00:00
-- url     : https://prove2.me/submissions/5322513e-29e4-4f5a-9e00-00ea5f2c1dd3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean:L45-L68
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.hessianB_mul. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian

-- ---- from OAI.Combinatorics.EuclideanRamsey.Hessian ----
namespace OAI

universe uDomain uCodomain uIndex uColor uAction

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial

open scoped BigOperators
open Matrix MeasureTheory
namespace EuclideanRamsey

section Hessian
variable {E : Type uDomain} {F : Type uCodomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma hessianB_mul {f g : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (x v w : E) :
    hessianB (fun y => f y*g y) x v w =
      f x*hessianB g x v w + g x*hessianB f x v w +
      fderiv ℝ f x v*fderiv ℝ g x w + fderiv ℝ g x v*fderiv ℝ f x w := by
  have hf' (x : E) := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' (x : E) := (hg.differentiable (by simp) x).hasFDerivAt
  have hG : (fun y => fderiv ℝ (fun z => f z*g z) y) =
      (fun y => f y • fderiv ℝ g y + g y • fderiv ℝ f y) := by
    funext y
    exact ((hf' y).mul (hg' y)).fderiv
  have hfd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hgd : Differentiable ℝ (fun y => fderiv ℝ g y) :=
    (hg.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have hd := ((hf' x).smul (hgd x).hasFDerivAt).add
    ((hg' x).smul (hfd x).hasFDerivAt)
  unfold hessianB
  rw [hG]
  change ((fderiv ℝ ((f • fun y => fderiv ℝ g y) + g • fun y => fderiv ℝ f y) x) v) w = _
  rw [hd.fderiv]
  simp only [_root_.add_apply, _root_.smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring

end Hessian

section Trace
variable {E : Type uDomain} {ι : Type uIndex} {κ : Type uColor} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Fintype ι] [Fintype κ]

end Trace

section MatrixContraction

end MatrixContraction

section Split
variable {E : Type uDomain} {H : Type uAction} [AddCommGroup E] [Module ℝ E] [AddCommGroup H] [Module ℝ H]

end Split

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open scoped BigOperators
open Matrix MeasureTheory


theorem solution.{uDomain} : type_of% @_root_.OAI.EuclideanRamsey.hessianB_mul.{uDomain} := @_root_.OAI.EuclideanRamsey.hessianB_mul.{uDomain}
