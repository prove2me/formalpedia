-- Prove2me | solution 1 for NonlinSSD.Discrete.eq_46_stdLagrangian_eq_lagrangian
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T16:29:15.919908+00:00
-- url     : https://prove2.me/submissions/9f0800f8-5422-4d74-825d-6bc26fd24df4

import Mathlib
import Definitions.Def_NonlinSSD_Discrete_Problem

open Finset

open NonlinSSD.Discrete in
theorem solution {m n N : ℕ} (p : Fin n → ℝ)
    (h : Fin n → (Fin N → ℝ) → ℝ) (g : Fin m → Fin n → (Fin N → ℝ) → ℝ)
    (y : Fin m → Fin n → ℝ) (μ : Fin m → Fin n → ℝ) :
    (∀ (i : Fin m) (X : Fin m → Fin n → ℝ),
      ∑ k, μ i k * ∑ j, p j * max (y i k - X i j) 0 =
        -∑ j, p j * multiplierUtility (y i) (μ i) (X i j)) ∧
    (∀ (z : Fin N → ℝ) (X θ : Fin m → Fin n → ℝ),
      stdLagrangian p h g y z X μ θ =
        lagrangian p h g y z X (fun i => multiplierUtility (y i) (μ i)) θ) := by
  have h1 : ∀ (i : Fin m) (X : Fin m → Fin n → ℝ),
      ∑ k, μ i k * ∑ j, p j * max (y i k - X i j) 0 =
        -∑ j, p j * multiplierUtility (y i) (μ i) (X i j) := by
    intro i X
    simp only [multiplierUtility, Finset.mul_sum, mul_neg, Finset.sum_neg_distrib, neg_neg]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  refine ⟨h1, ?_⟩
  intro z X θ
  have e : ∀ i, ∑ k, μ i k * ((∑ j, p j * max (y i k - y i j) 0) -
        ∑ j, p j * max (y i k - X i j) 0) =
      ∑ j, p j * (multiplierUtility (y i) (μ i) (X i j) -
        multiplierUtility (y i) (μ i) (y i j)) := by
    intro i
    have a := h1 i X
    have b := h1 i y
    rw [Finset.sum_congr rfl fun k _ => mul_sub (μ i k) _ _, Finset.sum_sub_distrib, a, b,
      Finset.sum_congr rfl fun j _ => mul_sub (p j) _ _, Finset.sum_sub_distrib]
    ring
  unfold stdLagrangian lagrangian
  simp_rw [e]
  have t : ∑ j, p j * ∑ i, θ i j * X i j = ∑ i, ∑ j, p j * (θ i j * X i j) := by
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  simp only [mul_sub, mul_add, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  simp only [Finset.mul_sum] at t
  rw [t]
  ring
