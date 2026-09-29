-- Prove2me | solution 1 for GeneralCK.regularizedEntropyBound_of_bellman
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T22:24:34.85068+00:00
-- url     : https://prove2.me/submissions/2dada47d-ee64-4710-9c53-39ee54bda3e0

import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_bellman
import Definitions.Def_GeneralCK_cube_analysis
import Definitions.Def_GeneralCK_entropy_comparison
import Definitions.Def_GeneralCK_entropy_flow
import Definitions.Def_GeneralCK_information
import Definitions.Def_GeneralCK_limit_transfer
import Definitions.Def_GeneralCK_noise_evolution
import Definitions.Def_GeneralCK_statement
import Theorems.Thm_GeneralCK_Flow_entropy_flow_bound
import Theorems.Thm_GeneralCK_noiseKernel_sum

open scoped BigOperators
namespace GeneralCK.Information
open scoped BigOperators









theorem kernel_symm {n : ℕ} (p : ℝ) (x y : Cube n) :
    noiseKernel p x y = noiseKernel p y x := by
  simp only [noiseKernel, eq_comm]

theorem kernel_column_sum {n : ℕ} (p : ℝ) (y : Cube n) :
    ∑ x, noiseKernel p x y = 1 := by
  simp_rw [kernel_symm p _ y]
  exact noiseKernel_sum p y

































end GeneralCK.Information

namespace GeneralCK.CubeAnalysis
open scoped BigOperators













theorem mean_const (n : ℕ) (c : ℝ) : mean (fun _ : Cube n => c) = c := by
  simp [mean, Cube, zpow_neg, zpow_natCast]















end GeneralCK.CubeAnalysis

namespace GeneralCK.Noise
open scoped BigOperators





























theorem applyNoise_indicator {n : ℕ} (f : Cube n → Bool) (p : ℝ) (y : Cube n) :
    applyNoise p (fun x => if f x = true then 1 else 0) y = Information.posterior f p y := by
  classical
  unfold applyNoise Information.posterior
  apply Finset.sum_congr rfl
  intro x _
  cases h : f x <;> simp [h]



theorem applyNoise_affine {n : ℕ} (p a b : ℝ) (v : Cube n → ℝ) (y : Cube n) :
    applyNoise p (fun x => a + b * v x) y = a + b * applyNoise p v y := by
  unfold applyNoise
  simp_rw [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [Information.kernel_column_sum, one_mul]
  simp_rw [mul_left_comm _ b, ← Finset.mul_sum]













end GeneralCK.Noise

namespace GeneralCK.Flow
open scoped BigOperators
open CubeAnalysis











theorem mean_add {n : ℕ} (v w : Cube n → ℝ) :
    mean (fun x => v x + w x) = mean v + mean w := by
  simp [mean, Finset.sum_add_distrib, mul_add]

theorem mean_const_mul {n : ℕ} (c : ℝ) (v : Cube n → ℝ) :
    mean (fun x => c * v x) = c * mean v := by
  simp only [mean, ← Finset.mul_sum]
  ring

theorem initialMean_eq {n : ℕ} (f : Cube n → Bool) (eps : ℝ) :
    initialMean f eps = eps + (1 - 2 * eps) * Information.meanIndicator f := by
  unfold initialMean regularized
  rw [mean_add, mean_const, mean_const_mul]
  rfl































end GeneralCK.Flow
namespace GeneralCK
end GeneralCK

open GeneralCK in
open scoped BigOperators in
theorem solution (hB : FiniteHybridBellman) :
    LimitTransfer.RegularizedEntropyBound := by
  intro n f eps p he he' hp hp'
  let T : ℝ := -Real.log (1 - 2 * p) / 2
  have harg : 0 < 1 - 2 * p := by linarith
  have harg' : 1 - 2 * p ≤ 1 := by linarith
  have hT : 0 ≤ T := by
    have hlog := Real.log_nonpos harg.le harg'
    dsimp [T]
    linarith
  have hexp : Real.exp (-2 * T) = 1 - 2 * p := by
    have h : -2 * T = Real.log (1 - 2 * p) := by dsimp [T]; ring
    rw [h, Real.exp_log harg]
  have hcross : Noise.crossover T = p := by unfold Noise.crossover; rw [hexp]; ring
  have hparam : Comparison.noiseParameter eps T = eps + p - 2 * eps * p := by
    unfold Comparison.noiseParameter
    rw [hexp]
    ring
  have hflow : Flow.flow f eps T = LimitTransfer.regularizedPosterior f p eps := by
    funext x
    unfold Flow.flow Flow.regularized LimitTransfer.regularizedPosterior
    rw [hcross, Noise.applyNoise_affine, Noise.applyNoise_indicator]
  have h := Flow.entropy_flow_bound hB f he he' hT
  rw [hparam] at h
  simpa only [Flow.delta, Flow.gamma, Flow.initialMean_eq, hflow,
    CubeAnalysis.mean, Information.cubeWeight, LimitTransfer.regularizedMean,
    Function.comp_apply] using h
