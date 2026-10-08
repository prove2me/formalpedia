-- Prove2me | solution 1 for MinimaxRegretRL.Bernstein.variance_le_two_sum
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T10:50:38.692695+00:00
-- url     : https://prove2.me/submissions/eacc09c4-0fdd-467e-af60-09e0f79557cf

import Mathlib
import Definitions.Def_MinimaxRegretRL_Bernstein_FiniteVariance

set_option autoImplicit false

open MinimaxRegretRL.Bernstein in
lemma finiteVar_eq_sum_sq_3c3fbad0 {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp1 : ∑ z, p z = 1) (f : Ω → ℝ) :
    finiteVar p f = ∑ z, p z * (f z - finiteExp p f) ^ 2 := by
  unfold finiteVar
  set m := finiteExp p f with hm
  have hm' : m = ∑ z, p z * f z := rfl
  rw [show (∑ z, p z * (f z - m) ^ 2) =
      ∑ z, (p z * f z ^ 2 - 2 * m * (p z * f z) + m ^ 2 * p z) from
      Finset.sum_congr rfl (fun z _ => by ring)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    hp1, ← hm']
  unfold finiteExp
  ring

open MinimaxRegretRL.Bernstein in
theorem solution {Ω : Type*} [Fintype Ω] (p : Ω → ℝ)
    (hp : ∀ z, 0 ≤ p z) (hp1 : ∑ z, p z = 1) (X Y : Ω → ℝ) :
    finiteVar p X ≤ 2 * (finiteVar p Y + finiteVar p (fun z => X z - Y z)) := by
  rw [finiteVar_eq_sum_sq_3c3fbad0 p hp1, finiteVar_eq_sum_sq_3c3fbad0 p hp1,
    finiteVar_eq_sum_sq_3c3fbad0 p hp1]
  have hE : finiteExp p X = finiteExp p Y + finiteExp p (fun z => X z - Y z) := by
    unfold finiteExp
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun z _ => by ring)
  rw [hE, ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z _
  set a := Y z - finiteExp p Y
  set b := X z - Y z - finiteExp p (fun z => X z - Y z)
  have hx : X z - (finiteExp p Y + finiteExp p (fun z => X z - Y z)) = a + b := by
    simp only [a, b]; ring
  rw [hx]
  nlinarith [mul_nonneg (hp z) (sq_nonneg (a - b))]
