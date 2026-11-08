-- Prove2me | solution 1 for MWMSLagrange.sum_sqrt_bound
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:33:21.474209+00:00
-- url     : https://prove2.me/submissions/94653f2a-bdc6-4e83-9c6e-1fda79342a02

import Mathlib
import Definitions.Def_MWMSLagrange_Instance
import Definitions.Def_MWMSLagrange_Instance_Nset
import Definitions.Def_MWMSLagrange_IsAllocation

open MWMSLagrange in
theorem solution {M N : ℕ} (I : Instance M N) (ρ : Fin N → Fin M → ℝ)
    (hρ : IsAllocation I ρ) :
    (∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2)
        ≤ Real.sqrt (M * ∑ j, ∑ i ∈ I.Nset j, ρ i j ^ 2)) ∧
      Real.sqrt (M * ∑ j, ∑ i ∈ I.Nset j, ρ i j ^ 2) ≤ Real.sqrt (M * N) ∧
      ∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2) ≤ N := by
  obtain ⟨hb, -, hrow⟩ := hρ
  have hnn : ∀ j, 0 ≤ ∑ i ∈ I.Nset j, ρ i j ^ 2 :=
    fun j => Finset.sum_nonneg (fun i _ => sq_nonneg _)
  have hS : ∑ j, ∑ i ∈ I.Nset j, ρ i j = N := by
    have : ∑ j, ∑ i ∈ I.Nset j, ρ i j = ∑ i, ∑ j ∈ I.Mset i, ρ i j := by
      simp only [Instance.Nset, Instance.Mset, Finset.sum_filter]
      exact Finset.sum_comm
    rw [this]
    simp [hrow]
  have hsq : ∀ j, ∑ i ∈ I.Nset j, ρ i j ^ 2 ≤ ∑ i ∈ I.Nset j, ρ i j := by
    intro j
    refine Finset.sum_le_sum (fun i _ => ?_)
    have h1 := hb i j
    nlinarith [h1.1, h1.2]
  refine ⟨?_, ?_, ?_⟩
  · rw [Real.le_sqrt (Finset.sum_nonneg (fun j _ => Real.sqrt_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun j _ => hnn j)))]
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun _ : Fin M => (1:ℝ))
      (fun j => Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2))
    simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one] at this
    calc (∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2)) ^ 2
        ≤ (M : ℝ) * ∑ j, Real.sqrt (∑ i ∈ I.Nset j, ρ i j ^ 2) ^ 2 := this
      _ = (M : ℝ) * ∑ j, ∑ i ∈ I.Nset j, ρ i j ^ 2 := by
        congr 1
        exact Finset.sum_congr rfl (fun j _ => Real.sq_sqrt (hnn j))
  · apply Real.sqrt_le_sqrt
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    rw [← hS]
    exact Finset.sum_le_sum (fun j _ => hsq j)
  · rw [← hS]
    refine Finset.sum_le_sum (fun j _ => ?_)
    have hpos : 0 ≤ ∑ i ∈ I.Nset j, ρ i j := Finset.sum_nonneg (fun i _ => (hb i j).1)
    rw [Real.sqrt_le_left hpos]
    exact Finset.sum_sq_le_sq_sum_of_nonneg (fun i _ => (hb i j).1)
