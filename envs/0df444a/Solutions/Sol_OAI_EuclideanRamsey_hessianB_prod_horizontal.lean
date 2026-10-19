-- Prove2me | solution 1 for OAI.EuclideanRamsey.hessianB_prod_horizontal
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T02:59:07.858981+00:00
-- url     : https://prove2.me/submissions/6b1f9080-387a-4d73-a231-0934c971a1bb

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Hessian.lean:L70-L85
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.hessianB_prod_horizontal. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Theorems.Thm_OAI_EuclideanRamsey_hessianB_linear_comp
import Theorems.Thm_OAI_EuclideanRamsey_hessianB_mul

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

lemma hessianB_prod_horizontal {f : E → ℝ} {g : F → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (x : E × F) (v w : E) :
    hessianB (fun x : E × F => f x.1*g x.2) x (v,0) (w,0) =
      g x.2*hessianB f x.1 v w := by
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => f x.1) := hf.comp contDiff_fst
  have hg2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : E×F => g x.2) := hg.comp contDiff_snd
  rw [hessianB_mul hf1 hg2]
  rw [show (fun x : E×F => f x.1) = f ∘ ContinuousLinearMap.fst ℝ E F from rfl,
    show (fun x : E×F => g x.2) = g ∘ ContinuousLinearMap.snd ℝ E F from rfl,
    hessianB_linear_comp hf, hessianB_linear_comp hg]
  have hfg := ((hg.differentiable (by simp) x.2).hasFDerivAt.comp x
    (ContinuousLinearMap.snd ℝ E F).hasFDerivAt).fderiv
  change fderiv ℝ (_ ∘ ⇑(ContinuousLinearMap.snd ℝ E F)) x = _ at hfg
  rw [hfg]
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


theorem solution.{uDomain,uCodomain} : type_of% @_root_.OAI.EuclideanRamsey.hessianB_prod_horizontal.{uDomain,uCodomain} := @_root_.OAI.EuclideanRamsey.hessianB_prod_horizontal.{uDomain,uCodomain}
