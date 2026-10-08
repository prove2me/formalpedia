-- Prove2me | solution 1 for MulticlassQNet.SingleStation.proof_8_4_projection_subset
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-05T14:57:51.913823+00:00
-- url     : https://prove2.me/submissions/976a50ca-36a3-46b8-a634-24609dedbba9

import Mathlib
import Definitions.Def_MulticlassQNet_SingleStation_Polyhedra



namespace MulticlassQNet.SingleStation

open Finset

theorem p2_key {n : ℕ} (lam mu : Fin n → ℝ) (hmu : ∀ i, 0 < mu i)
    (x : Fin n → ℝ) (I : Fin n → Fin n → ℝ) (h : (x, I) ∈ P2 lam mu) (S : Finset (Fin n)) :
    ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j =
      (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) + ∑ i ∈ S, rho lam mu i / mu i := by
  obtain ⟨_, _, hd, hoff, _⟩ := h
  simp only at hd hoff
  have hpair : ∀ i j, I i j / mu j + I j i / mu i =
      rho lam mu j * (1 / mu i * x i) + rho lam mu i * (1 / mu j * x j) +
        (if i = j then 2 * (rho lam mu i / mu i) else 0) := by
    intro i j
    have hi := hmu i; have hj := hmu j
    unfold rho
    by_cases hij : i = j
    · subst hij
      simp only [if_true]
      have := hd i
      field_simp
      nlinarith [this]
    · simp only [hij, if_false]
      have := hoff i j hij
      field_simp
      nlinarith [this]
  have h2 : 2 * ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j =
      ∑ i ∈ S, ∑ j ∈ S, (I i j / mu j + I j i / mu i) := by
    simp only [Finset.sum_add_distrib, Finset.sum_div]
    rw [Finset.sum_comm (f := fun i j => I j i / mu i)]
    rw [Finset.sum_comm (f := fun i j => I i j / mu j)]
    ring
  have h3 : ∑ i ∈ S, ∑ j ∈ S, (I i j / mu j + I j i / mu i) =
      2 * ((∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) + ∑ i ∈ S, rho lam mu i / mu i) := by
    simp only [hpair, Finset.sum_add_distrib]
    have e1 : ∑ i ∈ S, ∑ j ∈ S, rho lam mu j * (1 / mu i * x i) =
        (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) := by
      rw [Finset.sum_mul_sum, Finset.sum_comm]
    have e2 : ∑ i ∈ S, ∑ j ∈ S, rho lam mu i * (1 / mu j * x j) =
        (∑ i ∈ S, rho lam mu i) * (∑ i ∈ S, 1 / mu i * x i) := by
      rw [Finset.sum_mul_sum]
    have e3 : ∑ i ∈ S, ∑ j ∈ S, (if i = j then 2 * (rho lam mu i / mu i) else 0) =
        2 * ∑ i ∈ S, rho lam mu i / mu i := by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i hi
      rw [Finset.sum_ite_eq]; simp [hi]
    rw [e1, e2, e3]; ring
  linarith

theorem proj_subset_core {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} ⊆ P1 lam mu := by
  rintro x ⟨I, hI⟩
  have hI' := hI
  obtain ⟨hx, hInn, _, _, hcol⟩ := hI'
  simp only at hx hInn hcol
  have hrho : ∀ S : Finset (Fin n), ∑ i ∈ S, rho lam mu i < 1 := by
    intro S
    refine lt_of_le_of_lt ?_ hload
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S)
      (fun i _ _ => (div_pos (hlam i) (hmu i)).le)
  have hbound : ∀ S : Finset (Fin n), ∑ j ∈ S, (∑ i ∈ S, I i j) / mu j ≤ ∑ i ∈ S, 1 / mu i * x i := by
    intro S
    apply Finset.sum_le_sum
    intro j _
    rw [div_eq_inv_mul, one_div, ← hcol j]
    apply mul_le_mul_of_nonneg_left _ (inv_pos.mpr (hmu j)).le
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun i _ _ => hInn i j)
  have hfull : ∑ j ∈ (univ : Finset (Fin n)), (∑ i ∈ univ, I i j) / mu j =
      ∑ i ∈ (univ : Finset (Fin n)), 1 / mu i * x i := by
    apply Finset.sum_congr rfl
    intro j _
    rw [hcol j]; ring
  refine ⟨hx, ?_, ?_⟩
  · intro S _
    show b lam mu S ≤ _
    unfold b
    have h1 := hrho S
    rw [div_le_iff₀ (by linarith)]
    have := p2_key lam mu hmu x I hI S
    have := hbound S
    nlinarith
  · show _ = b lam mu univ
    unfold b
    have h1 := hrho univ
    rw [eq_div_iff (by linarith)]
    have := p2_key lam mu hmu x I hI univ
    rw [hfull] at this
    linarith

end MulticlassQNet.SingleStation

open MulticlassQNet.SingleStation


theorem solution {n : ℕ} (lam mu : Fin n → ℝ)
    (hlam : ∀ i, 0 < lam i) (hmu : ∀ i, 0 < mu i) (hload : ∑ i, lam i / mu i < 1) :
    {x : Fin n → ℝ | ∃ I, (x, I) ∈ P2 lam mu} ⊆ P1 lam mu := by
  exact proj_subset_core lam mu hlam hmu hload
