-- Prove2me | solution 1 for OAI.EuclideanRamsey.hessianB_linear_comp
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:55:26.63731+00:00
-- url     : https://prove2.me/submissions/57f29c76-db48-4379-885e-d10a888de98b

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean:L29-L43
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.hessianB_linear_comp. The node keeps its source
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

lemma hessianB_linear_comp {f : F → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : E →L[ℝ] F) (x v w : E) :
    hessianB (f ∘ L) x v w = hessianB f (L x) (L v) (L w) := by
  have hG : (fun y => fderiv ℝ (f ∘ L) y) =
      (fun y => (fderiv ℝ f (L y)).comp L) := by
    funext y
    exact ((hf.differentiable (by simp) (L y)).hasFDerivAt.comp y L.hasFDerivAt).fderiv
  have hd : Differentiable ℝ (fun y => fderiv ℝ f y) :=
    (hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).differentiable (by simp)
  have h := (((hd (L x)).hasFDerivAt.comp x L.hasFDerivAt).clm_comp
    (hasFDerivAt_const L x))
  dsimp only [Function.comp_def] at h
  unfold hessianB
  rw [hG, h.fderiv]
  simp

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


theorem solution.{uDomain,uCodomain} : type_of% @_root_.OAI.EuclideanRamsey.hessianB_linear_comp.{uDomain,uCodomain} := @_root_.OAI.EuclideanRamsey.hessianB_linear_comp.{uDomain,uCodomain}
