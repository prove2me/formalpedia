-- Prove2me | solution 1 for OAI.EuclideanRamsey.compact_taylor_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-10-18T03:11:31.126725+00:00
-- url     : https://prove2.me/submissions/18fd4769-8d50-4338-9d31-1a1e894315d3

-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/EuclideanRamsey/Discretization.lean:L23-L59
-- (upload_full_project.md Phase 4): solution for node OAI.EuclideanRamsey.compact_taylor_bound. The node keeps its source
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

-- ---- from OAI.Combinatorics.EuclideanRamsey.Discretization ----
namespace OAI

universe uDomain uIndex

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

open MeasureTheory
open scoped BigOperators
namespace EuclideanRamsey

lemma compact_taylor_bound {E : Type uDomain} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : E → ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ x h : E,
      |f (x+h)-f x-fderiv ℝ f x h-
        (1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h]| ≤ K*‖h‖^3 := by
  obtain ⟨K,hK⟩ := (hf.continuous_iteratedFDeriv (m := 3) (by norm_cast)).bounded_above_of_compact_support
    (hfc.iteratedFDeriv 3)
  have hK0 : 0 ≤ K := (norm_nonneg _).trans (hK 0)
  refine ⟨K,hK0,?_⟩
  intro x h
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv (n := 2) (f := f) (x := x) (y := h)
    (fun t ht => (hf.of_le (by norm_cast)).contDiffAt)
  have he : f (x+h)-f x-fderiv ℝ f x h-(1/2:ℝ)*iteratedFDeriv ℝ 2 f x ![h,h] =
      (1/2:ℝ)*∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h) := by
    have hvec : (fun _ : Fin 2 => h) = ![h,h] := by ext i; fin_cases i <;> rfl
    simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add,Nat.factorial,
      Nat.cast_one,Nat.cast_mul,inv_one,
      iteratedFDeriv_zero_apply,iteratedFDeriv_one_apply,smul_eq_mul,hvec] at ht
    linarith
  rw [he,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)]
  have hi : |∫ t in (0:ℝ)..1, (1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)| ≤
      K*‖h‖^3 := by
    have ht (t : ℝ) (ht : t ∈ Set.Icc (0:ℝ) 1) :
        ‖(1-t)^2 * iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 := by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have hm := (iteratedFDeriv ℝ 3 f (x+t • h)).le_opNorm (fun _ => h)
      simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hm
      have hd : ‖iteratedFDeriv ℝ 3 f (x+t • h) (fun _ => h)‖ ≤ K*‖h‖^3 :=
        hm.trans (mul_le_mul_of_nonneg_right (hK _) (by positivity))
      have ht2 : (1-t)^2 ≤ 1 := by nlinarith [ht.1,ht.2]
      calc
        _ ≤ 1 * (K*‖h‖^3) := mul_le_mul ht2 hd (norm_nonneg _) (by norm_num)
        _ = _ := one_mul _
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0:ℝ)) (b := 1)
      (C := K*‖h‖^3) (fun t ht' => ht t ⟨(by simpa using ht'.1 : 0 < t).le,by simpa using ht'.2⟩)
    simpa using hh
  nlinarith [mul_nonneg hK0 (pow_nonneg (norm_nonneg h) 3)]

end EuclideanRamsey

open scoped BigOperators
namespace EuclideanRamsey

end EuclideanRamsey

open scoped BigOperators Pointwise Topology
open MeasureTheory Filter
namespace EuclideanRamsey

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
open MeasureTheory
open scoped BigOperators


theorem solution.{uDomain} : type_of% @_root_.OAI.EuclideanRamsey.compact_taylor_bound.{uDomain} := @_root_.OAI.EuclideanRamsey.compact_taylor_bound.{uDomain}
