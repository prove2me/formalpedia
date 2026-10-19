-- Prove2me | solution 1 for LocalDistanceNetwork.variance_linear_estimator
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T04:43:05.297234+00:00
-- url     : https://prove2.me/submissions/b4dec856-7b7a-4cea-a84e-763a89fa7729

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS
open Matrix LocalDistanceNetwork MeasureTheory ProbabilityTheory

namespace GLSVar

lemma var_linear {m n : Type*} [Fintype m] [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Matrix m m ℝ) (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (A : Matrix m n ℝ) (X₀ : n → ℝ) (L : Matrix n m ℝ) (v : n → ℝ) :
    Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] = v ⬝ᵥ (linearEstimatorCov L C *ᵥ v) := by
  set w := Lᵀ *ᵥ v with hw
  set c := v ⬝ᵥ (L *ᵥ (A *ᵥ X₀)) with hc
  have hfun : (fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω))) =
      fun ω => c + ∑ i, w i * ε ω i := by
    funext ω
    rw [mulVec_add, dotProduct_add]
    congr 1
    rw [dotProduct_mulVec, ← mulVec_transpose]
    rfl
  have hmem : ∀ i, MemLp (fun ω => w i * ε ω i) 2 μ := fun i => (hε i).const_mul (w i)
  have hS : MemLp (fun ω => ∑ i, w i * ε ω i) 2 μ := memLp_finsetSum _ fun i _ => hmem i
  rw [hfun, variance_const_add hS.aestronglyMeasurable, ← covariance_self hS.aemeasurable,
    covariance_fun_sum_fun_sum hmem hmem]
  simp only [covariance_const_mul_left, covariance_const_mul_right, hcov]
  unfold linearEstimatorCov
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, ← mulVec_transpose, ← hw]
  simp only [dotProduct, mulVec, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

end GLSVar

theorem solution {m n : Type*} [Fintype m] [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Matrix m m ℝ) (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (A : Matrix m n ℝ) (X₀ : n → ℝ) (L : Matrix n m ℝ) (v : n → ℝ) :
    Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] = v ⬝ᵥ (linearEstimatorCov L C *ᵥ v) :=
  GLSVar.var_linear μ C ε hε hcov A X₀ L v
