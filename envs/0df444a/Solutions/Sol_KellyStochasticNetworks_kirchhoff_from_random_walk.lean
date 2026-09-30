-- Prove2me | solution 1 for KellyStochasticNetworks.kirchhoff_from_random_walk
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-26T21:44:33.189798+00:00
-- url     : https://prove2.me/submissions/2e715e5f-30fd-4620-b7d9-f272dcb27bfa

import Mathlib

namespace KellyStochasticNetworks

open Finset

end KellyStochasticNetworks

open KellyStochasticNetworks
theorem solution {n : ℕ} (γ : Fin n → Fin n → ℝ) (p : Fin n → ℝ)
    (S : Finset (Fin n)) (hsym : ∀ i j, γ i j = γ j i)
    (hdeg : ∀ j, j ∉ S → 0 < ∑ k, γ j k)
    (hp : ∀ j, j ∉ S → p j = ∑ i, (γ j i / ∑ k, γ j k) * p i) :
    ∀ j, j ∉ S → (∑ i, γ i j * (p i - p j)) = 0 := by
  intro j hj
  have hdegpos := hdeg j hj
  have key : (∑ k, γ j k) * p j = ∑ i, γ j i * p i := by
    conv_lhs => rw [hp j hj]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    field_simp
  have expand : ∑ i, γ i j * (p i - p j) = (∑ i, γ i j * p i) - (∑ i, γ i j) * p j := by
    rw [Finset.sum_mul]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [expand]
  have hsymsum : ∑ i, γ i j = ∑ k, γ j k := by
    apply Finset.sum_congr rfl
    intro i _
    exact hsym i j
  rw [hsymsum]
  have hsymprod : ∑ i, γ i j * p i = ∑ i, γ j i * p i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym i j]
  rw [hsymprod, key]
  ring

