-- Prove2me | solution 1 for OAI.EuclideanRamsey.stencil_taylor_uniform
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:25:05.085188+00:00
-- url     : https://prove2.me/submissions/ef9b7728-39f8-4d5a-8073-fc650f08edd0

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/StencilConvolution.lean:L26-L84
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.stencil_taylor_uniform. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_EuclideanRamsey
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorNecessity
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_TensorDescent
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingKernel
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Hessian
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_DifferentialSplitting
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_SmoothingMatrix
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_LatticeMoments
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Discretization
import Theorems.Thm_OAI_EuclideanRamsey_bilinear_moment_contract
import Theorems.Thm_OAI_EuclideanRamsey_compact_taylor_bound
import Theorems.Thm_OAI_EuclideanRamsey_linear_moment_contract

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

lemma hessianB_eq (f : E → ℝ) (x v w : E) :
    hessianB f x v w = iteratedFDeriv ℝ 2 f x ![v,w] := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_one_apply]
  rfl

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

-- ---- from OAI.Combinatorics.EuclideanRamsey.StencilConvolution ----
namespace OAI

universe uIndex

noncomputable section

open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology

namespace EuclideanRamsey
open scoped BigOperators

lemma stencil_taylor_uniform {ι : Type uIndex} {k : ℕ} (S : Finset ι)
    (q : ι → ℝ) (v : ι → (Fin k → ℝ)) (C : Matrix (Fin k) (Fin k) ℝ)
    (hzero : ∑ γ ∈ S,q γ = 0) (hfirst : ∀ j,∑ γ ∈ S,q γ*v γ j = 0)
    (hsecond : ∀ j l,∑ γ ∈ S,q γ*v γ j*v γ l = C j l)
    {b : (Fin k → ℝ) → ℝ} (hb : ContDiff ℝ (⊤ : ℕ∞) b)
    (hbc : HasCompactSupport b) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (t : ℝ), 0 < t → ∀ x,
      |t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x| ≤ K/t := by
  obtain ⟨K,hK,hTaylor⟩ := compact_taylor_bound hb hbc
  refine ⟨∑ γ ∈ S, |q γ| *K*‖v γ‖^3,Finset.sum_nonneg (fun _ _ => by positivity),?_⟩
  intro t ht x
  have hl := linear_moment_contract S q v (fderiv ℝ b x)
  simp only [hfirst,zero_mul,Finset.sum_const_zero] at hl
  have hb' := bilinear_moment_contract S q v (hessianB b x)
  simp only [hsecond,hessianB_eq] at hb'
  let r (γ : ι) := b (x+(-t⁻¹) • v γ)-b x-
    fderiv ℝ b x ((-t⁻¹) • v γ)-
    (1/2:ℝ)*iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ]
  have hr (γ : ι) : |r γ| ≤ K*(t⁻¹)^3*‖v γ‖^3 := by
    have hh := hTaylor x ((-t⁻¹) • v γ)
    simpa only [r,norm_smul,Real.norm_eq_abs,abs_neg,abs_inv,abs_of_pos ht,mul_pow,
      mul_assoc] using hh
  have hrEq : t^2*(∑ γ ∈ S,q γ*b (x+(-t⁻¹) • v γ))-stencilDifferential C b x =
      t^2*∑ γ ∈ S,q γ*r γ := by
    have hscale (γ : ι) : iteratedFDeriv ℝ 2 b x ![(-t⁻¹) • v γ,(-t⁻¹) • v γ] =
        (t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ] := by
      simp only [← hessianB_eq,map_smul,_root_.smul_apply,smul_eq_mul]
      ring
    simp only [r,mul_sub,Finset.sum_sub_distrib,map_smul,smul_eq_mul,hscale]
    have hz : ∑ γ ∈ S,q γ*b x = 0 := by rw [← Finset.sum_mul,hzero,zero_mul]
    have h1 : ∑ γ ∈ S,q γ*(-t⁻¹*fderiv ℝ b x (v γ)) = 0 := by
      calc
        _ = -t⁻¹*(∑ γ ∈ S,q γ*fderiv ℝ b x (v γ)) := by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro γ hγ; ring
        _ = 0 := by rw [hl,mul_zero]
    have h2 : ∑ γ ∈ S,q γ*((1/2:ℝ)*((t⁻¹)^2*iteratedFDeriv ℝ 2 b x ![v γ,v γ])) =
        (t⁻¹)^2*stencilDifferential C b x := by
      unfold stencilDifferential
      rw [← hb']
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ hγ
      ring
    rw [hz,h1,h2]
    field_simp
    ring
  rw [hrEq,abs_mul,abs_of_nonneg (sq_nonneg t)]
  calc
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *|r γ| := by
      gcongr
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun γ => q γ*r γ) S
    _ ≤ t^2 * ∑ γ ∈ S, |q γ| *(K*(t⁻¹)^3*‖v γ‖^3) := by
      gcongr with γ hγ
      exact hr γ
    _ = (∑ γ ∈ S,|q γ| *K*‖v γ‖^3)/t := by
      rw [Finset.mul_sum,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro γ hγ
      field_simp

end EuclideanRamsey

namespace EuclideanRamsey
open MeasureTheory Filter
open scoped BigOperators Topology

end EuclideanRamsey

namespace EuclideanRamsey
open Filter MeasureTheory
open scoped BigOperators Topology

end EuclideanRamsey

namespace EuclideanRamsey
open scoped BigOperators

end EuclideanRamsey

end

end OAI

-- ---- platform node ----
open OAI OAI.EuclideanRamsey
open scoped TensorProduct RealInnerProductSpace
open scoped BigOperators
open Real Filter Topology MeasureTheory Polynomial
open Matrix MeasureTheory
open MeasureTheory
open Matrix
open scoped MatrixOrder Matrix.Norms.L2Operator
open MeasureTheory Matrix
open scoped TensorProduct
open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
open scoped BigOperators Pointwise
open scoped BigOperators Topology
open scoped BigOperators


theorem solution.{uIndex} : type_of% @_root_.OAI.EuclideanRamsey.stencil_taylor_uniform.{uIndex} := @_root_.OAI.EuclideanRamsey.stencil_taylor_uniform.{uIndex}
