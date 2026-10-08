-- Prove2me | solution 1 for LogSobolevMC.Entropy.entL_eq_relEnt
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T14:21:52.777678+00:00
-- url     : https://prove2.me/submissions/7250b963-a014-43f0-acee-36d44ac2e7ca

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_mm_continuous
import Definitions.Def_LogSobolevMC_Entropy_Setting



namespace LogSobolevMC.Entropy

open scoped BigOperators

theorem entL_eq_relEnt_core {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hf2 : LogSobolevMC.ChiSquare.lpNorm π 2 f = 1) :
    LogSobolevMC.ChiSquare.entL π f = relEnt π (fun x => f x ^ 2 * π x) := by
  unfold LogSobolevMC.ChiSquare.entL relEnt
  rw [hf2]
  apply Finset.sum_congr rfl
  intro x _
  have h1 : |f x| ^ (2:ℝ) = f x ^ 2 := by
    rw [abs_of_nonneg (hf x), Real.rpow_two]
  rw [h1, Real.one_rpow, div_one]
  have h2 : f x ^ 2 * π x / π x = f x ^ 2 := by
    rw [mul_div_assoc, div_self (hπpos x).ne', mul_one]
  rw [h2]
  ring

end LogSobolevMC.Entropy

open LogSobolevMC.Entropy


theorem solution {V : Type*} [Fintype V] [DecidableEq V]
    (π : V → ℝ) (hπ : MarkovMixing.IsDist π) (hπpos : ∀ x, 0 < π x)
    (f : V → ℝ) (hf : ∀ x, 0 ≤ f x) (hf2 : LogSobolevMC.ChiSquare.lpNorm π 2 f = 1) :
    LogSobolevMC.ChiSquare.entL π f = relEnt π (fun x => f x ^ 2 * π x) := by
  exact entL_eq_relEnt_core π hπ hπpos f hf hf2
