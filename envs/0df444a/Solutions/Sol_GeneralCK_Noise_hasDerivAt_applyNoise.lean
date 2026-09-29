-- Prove2me | solution 1 for GeneralCK.Noise.hasDerivAt_applyNoise
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-24T21:51:47.3693+00:00
-- url     : https://prove2.me/submissions/b84c385b-87c2-4c58-a4e7-eaa0e24e2d8d

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
import Definitions.Def_GeneralCK_noise_evolution
import Definitions.Def_GeneralCK_statement

open scoped BigOperators
namespace GeneralCK.Noise
open scoped BigOperators







theorem hasDerivAt_crossover (t : ℝ) :
    HasDerivAt crossover (Real.exp (-2 * t)) t := by
  have h := (((hasDerivAt_id t).const_mul (-2)).exp.const_sub 1).div_const 2
  convert! h using 1; dsimp [crossover]; ring



theorem factor_derivative (a b : Bool) (t : ℝ) :
    HasDerivAt (fun s => factor (crossover s) a b)
      (factor (crossover t) a (!b) - factor (crossover t) a b) t := by
  cases a <;> cases b <;> simp only [factor, Bool.false_eq_true, Bool.true_eq_false,
    Bool.not_false, Bool.not_true, ite_true, ite_false]
  · convert! (hasDerivAt_crossover t).const_sub 1 using 1; dsimp [crossover]; ring
  · convert! hasDerivAt_crossover t using 1; dsimp [crossover]; ring
  · convert! hasDerivAt_crossover t using 1; dsimp [crossover]; ring
  · convert! (hasDerivAt_crossover t).const_sub 1 using 1; dsimp [crossover]; ring

theorem kernel_flip_difference {n : ℕ} (p : ℝ) (x y : Cube n) (i : Fin n) :
    noiseKernel p x (flip y i) - noiseKernel p x y =
      (∏ j ∈ Finset.univ.erase i, factor p (x j) (y j)) *
        (factor p (x i) (!(y i)) - factor p (x i) (y i)) := by
  classical
  change (∏ j, factor p (x j) (flip y i j)) - (∏ j, factor p (x j) (y j)) = _
  rw [← Finset.prod_erase_mul _ (fun j => factor p (x j) (flip y i j)) (Finset.mem_univ i),
    ← Finset.prod_erase_mul _ (fun j => factor p (x j) (y j)) (Finset.mem_univ i)]
  have he : (∏ j ∈ Finset.univ.erase i, factor p (x j) (flip y i j)) =
      ∏ j ∈ Finset.univ.erase i, factor p (x j) (y j) := by
    apply Finset.prod_congr rfl
    intro j hj
    simp [flip, Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  simp only [flip, Function.update_self]
  ring

theorem hasDerivAt_kernel {n : ℕ} (x y : Cube n) (t : ℝ) :
    HasDerivAt (fun s => noiseKernel (crossover s) x y)
      (∑ i, (noiseKernel (crossover t) x (flip y i) - noiseKernel (crossover t) x y)) t := by
  have h := HasDerivAt.fun_finsetProd (u := Finset.univ)
    (fun (i : Fin n) _ => factor_derivative (x i) (y i) t)
  convert! h using 1
  simp only [smul_eq_mul, ← kernel_flip_difference]































end GeneralCK.Noise

open GeneralCK GeneralCK.Noise in
theorem solution {n : ℕ} (v : Cube n → ℝ) (y : Cube n) (t : ℝ) :
    HasDerivAt (fun s => applyNoise (crossover s) v y)
      (∑ i, (applyNoise (crossover t) v (flip y i) - applyNoise (crossover t) v y)) t := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun (x : Cube n) _ => (hasDerivAt_kernel x y t).mul_const (v x))
  convert! h using 1
  simp only [applyNoise, Finset.sum_mul, sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_comm]
  · rw [Finset.sum_comm]
