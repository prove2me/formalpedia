-- Prove2me | solution 1 for MetricTSPSublinear.sample_hits_large_sets
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-11-27T05:01:08.915206+00:00
-- url     : https://prove2.me/submissions/5d9a32c8-b6e6-4de6-ba25-c76ae8b05059

import Mathlib

namespace MTSPHIT

open Finset

/-- Tuples avoiding a set: exactly `(K - |A|)^s` of the `K^s` tuples. -/
theorem card_avoid (K s : ℕ) (A : Finset (Fin K)) :
    (univ.filter (fun u : Fin s → Fin K => ∀ i, u i ∉ A)).card = (K - A.card) ^ s := by
  have : (univ.filter (fun u : Fin s → Fin K => ∀ i, u i ∉ A)) = Fintype.piFinset (fun _ => Aᶜ) := by
    ext u; simp [Fintype.mem_piFinset]
  rw [this, Fintype.card_piFinset]
  simp [card_compl]

/-- `(K - a)^s ≤ K^s · exp(-a s / K)`. -/
theorem avoid_le_exp (K s a : ℕ) (ha : a ≤ K) (hK : 0 < K) :
    (((K - a) ^ s : ℕ) : ℝ) ≤ (K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K) := by
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK
  have h1 : (((K - a : ℕ)) : ℝ) = K * (1 - a / K) := by
    rw [Nat.cast_sub ha]; field_simp
  push_cast [Nat.cast_pow]
  rw [h1, mul_pow]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have h2 : 0 ≤ 1 - (a : ℝ) / K := by
    rw [sub_nonneg, div_le_one hK']; exact_mod_cast ha
  calc (1 - (a : ℝ) / K) ^ s ≤ (Real.exp (-(a / K))) ^ s := by
        apply pow_le_pow_left₀ h2
        have := Real.add_one_le_exp (-(a / K : ℝ)); linarith
    _ = Real.exp (-(a : ℝ) * s / K) := by
        rw [← Real.exp_nat_mul]; congr 1; ring

/-- **Hitting a family of large sets.** If each of the sets `A j` (`j` in a finite index type `J`) has at least `a`
elements of `Fin K`, then the number of `s`-tuples that miss some `A j` is at most
`|J| · K^s · exp(-a s / K)`. -/
theorem miss_some_le {J : Type*} [Fintype J] (K s a : ℕ) (hK : 0 < K) (A : J → Finset (Fin K))
    (hA : ∀ j, a ≤ (A j).card) :
    ((univ.filter (fun u : Fin s → Fin K => ∃ j, ∀ i, u i ∉ A j)).card : ℝ) ≤
      (Fintype.card J : ℝ) * ((K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K)) := by
  classical
  have hsub : (univ.filter (fun u : Fin s → Fin K => ∃ j, ∀ i, u i ∉ A j)) ⊆
      univ.biUnion (fun j => univ.filter (fun u : Fin s → Fin K => ∀ i, u i ∉ A j)) := by
    intro u hu; simp only [mem_filter, mem_univ, true_and] at hu
    obtain ⟨j, hj⟩ := hu; exact mem_biUnion.mpr ⟨j, mem_univ _, by simp [hj]⟩
  calc ((univ.filter (fun u : Fin s → Fin K => ∃ j, ∀ i, u i ∉ A j)).card : ℝ)
      ≤ ((univ.biUnion (fun j => univ.filter (fun u : Fin s → Fin K => ∀ i, u i ∉ A j))).card : ℝ) := by
        exact_mod_cast card_le_card hsub
    _ ≤ ∑ j, ((univ.filter (fun u : Fin s → Fin K => ∀ i, u i ∉ A j)).card : ℝ) := by
        exact_mod_cast card_biUnion_le
    _ ≤ ∑ _j : J, ((K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K)) := by
        apply sum_le_sum; intro j _
        rw [card_avoid]
        have hle : (A j).card ≤ K := by simpa using card_le_univ (A j)
        calc (((K - (A j).card) ^ s : ℕ) : ℝ) ≤ (K : ℝ) ^ s * Real.exp (-((A j).card : ℝ) * s / K) :=
              avoid_le_exp K s _ hle hK
          _ ≤ (K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Real.exp_le_exp.mpr
              have : (a : ℝ) ≤ (A j).card := by exact_mod_cast hA j
              have hK' : (0 : ℝ) < K := by exact_mod_cast hK
              rw [div_le_div_iff_of_pos_right hK']
              have hs : (0 : ℝ) ≤ s := by positivity
              nlinarith
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]

end MTSPHIT

open MTSPHIT in
theorem solution {J : Type*} [Fintype J] (K s a : ℕ) (hK : 0 < K) (A : J → Finset (Fin K))
    (hA : ∀ j, a ≤ (A j).card) :
    ((Finset.univ.filter (fun u : Fin s → Fin K => ∃ j, ∀ i, u i ∉ A j)).card : ℝ) ≤
      (Fintype.card J : ℝ) * ((K : ℝ) ^ s * Real.exp (-(a : ℝ) * s / K)) :=
  MTSPHIT.miss_some_le K s a hK A hA
