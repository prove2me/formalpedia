-- Prove2me | solution 1 for LogSobolevMC.Entropy.density_measHeat
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:21:02.202454+00:00
-- url     : https://prove2.me/submissions/88f0514d-e635-47c3-9334-34d79674141f

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting



namespace LogSobolevMC.Entropy

open scoped BigOperators

/-- powers of the time reversal -/
lemma timeReversal_pow_apply {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π : V → ℝ) (hπpos : ∀ x, 0 < π x) (k : ℕ) (x y : V) :
    ((MarkovMixing.timeReversal K π) ^ k) x y = π y * (K ^ k) y x / π x := by
  induction k generalizing x y with
  | zero =>
    simp only [pow_zero, Matrix.one_apply]
    by_cases h : x = y
    · subst h; simp; rw [div_self (hπpos x).ne']
    · simp [h, Ne.symm h]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp_rw [ih]
    unfold MarkovMixing.timeReversal
    rw [pow_succ', Matrix.mul_apply]
    rw [Finset.mul_sum, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro z _
    have := (hπpos x).ne'
    have := (hπpos z).ne'
    field_simp

lemma heatKernel_timeReversal {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (π : V → ℝ) (hπpos : ∀ x, 0 < π x) (t : ℝ) (x y : V) :
    MarkovMixing.heatKernel (MarkovMixing.timeReversal K π) t x y
      = π y * MarkovMixing.heatKernel K t y x / π x := by
  unfold MarkovMixing.heatKernel
  simp_rw [timeReversal_pow_apply K π hπpos]
  rw [← tsum_mul_left, ← tsum_div_const]
  apply tsum_congr
  intro k
  ring

theorem density_measHeat_core {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (t : ℝ) :
    measHeat K t (fun x => f x * π x) =
      fun y => LogSobolevMC.ChiSquare.heatOp (MarkovMixing.timeReversal K π) t f y * π y := by
  funext y
  unfold measHeat LogSobolevMC.ChiSquare.heatOp
  rw [Matrix.vecMul, Matrix.mulVec, dotProduct, dotProduct, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  rw [heatKernel_timeReversal K π hπpos]
  have := (hπpos y).ne'
  field_simp

end LogSobolevMC.Entropy

open LogSobolevMC.Entropy


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (K : Matrix V V ℝ) (hK : MarkovMixing.IsStochastic K)
    (π : V → ℝ) (hπ : MarkovMixing.IsStationary K π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (t : ℝ) :
    measHeat K t (fun x => f x * π x) =
      fun y => LogSobolevMC.ChiSquare.heatOp (MarkovMixing.timeReversal K π) t f y * π y := by
  exact density_measHeat_core K hK π hπ hπpos f t
