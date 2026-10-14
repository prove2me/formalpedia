-- Prove2me | solution 1 for MultiIndex.alternating_binomial_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-12T17:30:46.803891+00:00
-- url     : https://prove2.me/submissions/016baa77-56d4-49a7-8da9-29c9f9713fec

import Theorems.Thm_Nat_alternating_choose_convolution
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.Pi

open Finset

set_option autoImplicit false

theorem solution {ι R : Type*} [Fintype ι] [CommRing R]
    (α : ι → ℕ) (s : Finset (ι → ℕ))
    (hs : ∀ β : ι → ℕ, (∀ i, β i ≤ α i) → β ∈ s)
    (F : (ι → ℕ) → (ι → ℕ) → R) :
    (∑ β ∈ s, (∏ i, (Nat.choose (α i) (β i) : R)) *
      (-1 : R) ^ (∑ i, β i) *
      (∑ γ ∈ s, (∏ i, (Nat.choose (β i) (γ i) : R)) *
        F (fun i => α i - β i + (β i - γ i)) γ)) =
      (-1 : R) ^ (∑ i, α i) * F (fun _ => 0) α := by
  classical
  let C : (ι → ℕ) → (ι → ℕ) → R := fun a b => ∏ i, (Nat.choose (a i) (b i) : R)
  have cz : ∀ a b, ¬ (∀ i, b i ≤ a i) → C a b = 0 := by
    intro a b h
    obtain ⟨i, hi⟩ := not_forall.mp h
    apply prod_eq_zero (mem_univ i)
    simp [Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)]
  let box := Fintype.piFinset (fun i => range (α i + 1))
  have mb : ∀ b, b ∈ box ↔ ∀ i, b i ≤ α i := by
    intro b
    simp [box, Fintype.mem_piFinset]
  have bs : box ⊆ s := fun b hb => hs b ((mb b).mp hb)
  have coeff : ∀ γ : ι → ℕ,
      (∑ β ∈ s, C α β * (-1 : R)^(∑ i, β i) * C β γ) =
        if γ = α then (-1 : R)^(∑ i, α i) else 0 := by
    intro γ
    have restrict : (∑ β ∈ s, C α β * (-1 : R)^(∑ i, β i) * C β γ) =
        ∑ β ∈ box, C α β * (-1 : R)^(∑ i, β i) * C β γ := by
      symm
      apply sum_subset bs
      intro b hb hn
      simp [cz α b (by simpa [← mb] using hn)]
    rw [restrict]
    have factor : (∑ β ∈ box, C α β * (-1 : R)^(∑ i, β i) * C β γ) =
        ∏ i, ∑ k ∈ range (α i + 1),
          (Nat.choose (α i) k : R) * (-1 : R)^k * (Nat.choose k (γ i) : R) := by
      rw [prod_univ_sum]
      apply sum_congr rfl
      intro b hb
      simp only [C, ← prod_mul_distrib, ← prod_pow_eq_pow_sum]
    rw [factor]
    simp_rw [Nat.alternating_choose_convolution]
    by_cases he : γ = α
    · subst γ
      simp [← prod_pow_eq_pow_sum]
    · rw [if_neg he]
      have hn : ∃ i, γ i ≠ α i := by
        by_contra h
        apply he
        funext i
        exact not_not.mp (not_exists.mp h i)
      obtain ⟨i, hi⟩ := hn
      exact prod_eq_zero (mem_univ i) (if_neg hi)
  change (∑ β ∈ s, C α β * (-1 : R)^(∑ i, β i) *
      (∑ γ ∈ s, C β γ * F (fun i => α i - β i + (β i - γ i)) γ)) = _
  simp_rw [mul_sum]
  have flatten : (∑ β ∈ s, ∑ γ ∈ s,
      C α β * (-1 : R)^(∑ i, β i) *
        (C β γ * F (fun i => α i - β i + (β i - γ i)) γ)) =
      ∑ β ∈ s, ∑ γ ∈ s,
        (C α β * (-1 : R)^(∑ i, β i) * C β γ) *
          F (fun i => α i - γ i) γ := by
    apply sum_congr rfl
    intro β hβ
    apply sum_congr rfl
    intro γ hγ
    by_cases hb : ∀ i, β i ≤ α i
    · by_cases hg : ∀ i, γ i ≤ β i
      · have hf : (fun i => α i - β i + (β i - γ i)) = (fun i => α i - γ i) := by
          funext i
          have := hb i
          have := hg i
          omega
        simp only [hf, mul_assoc]
      · simp [cz β γ hg]
    · simp [cz α β hb]
  rw [flatten, sum_comm]
  simp_rw [← sum_mul, coeff]
  rw [sum_eq_single α]
  · simp
  · intro γ hγ hne
    simp [hne]
  · exact fun h => (h (hs α (fun _ => le_rfl))).elim
