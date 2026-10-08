-- Prove2me | solution 1 for Gomory69.Asymptotic.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T20:53:58.697399+00:00
-- url     : https://prove2.me/submissions/21281ab4-a0ea-4791-8bce-6a2bd54274a3

import Mathlib
import Definitions.Def_Gomory69_Asymptotic_GroupPolyhedron
import Definitions.Def_Gomory69_Asymptotic_IntegerProgram



namespace Gomory69.Asymptotic

theorem thm1_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by
  classical
  let S : Finset (↥𝒩 → ℕ) := Fintype.piFinset (fun g => Finset.range (t g + 1))
  have hcard : S.card = ∏ g : ↥𝒩, (1 + t g) := by
    simp [S, Fintype.card_piFinset, add_comm]
  let φ : (↥𝒩 → ℕ) → G := fun s => ∑ g, s g • (g : G)
  have hinj : Set.InjOn φ S := by
    intro s hs r hr h
    simp only [S, Finset.mem_coe, Fintype.mem_piFinset, Finset.mem_range] at hs hr
    have := ht (fun g => (r g : ℤ)) (fun g => (s g : ℤ))
      (fun g => ⟨by positivity, by have := hr g; omega⟩)
      (fun g => ⟨by positivity, by have := hs g; omega⟩)
      (by simpa [φ, natCast_zsmul] using h.symm)
    funext g
    have := congrFun this g
    simpa using this
  have : S.card ≤ (Finset.univ : Finset G).card :=
    Finset.card_le_card_of_injOn φ (fun _ _ => Finset.mem_univ _) hinj
  rw [← hcard]; simpa using this

theorem one_add_sum_le_prod {ι : Type*} [Fintype ι] (t : ι → ℕ) :
    1 + ∑ i, t i ≤ ∏ i, (1 + t i) := by
  classical
  have : ∀ s : Finset ι, 1 + ∑ i ∈ s, t i ≤ ∏ i ∈ s, (1 + t i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      nlinarith [Nat.zero_le (t a), Nat.zero_le (∑ i ∈ s, t i)]
  exact this Finset.univ

theorem sum_le_core {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∑ g : ↥𝒩, t g ≤ Fintype.card G - 1 := by
  have h1 := thm1_core 𝒩 h𝒩 t ht
  have h2 := one_add_sum_le_prod t
  omega

theorem thm2_core {G : Type*} [AddCommGroup G] [Finite G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (g₀ : G) (v : ↥𝒩 → ℝ)
    (hv : v ∈ Set.extremePoints ℝ (groupPolyhedron 𝒩 g₀)) :
    ∃ t ∈ groupSolutions 𝒩 g₀, toReal 𝒩 t = v ∧ IsIrreducible 𝒩 t := by
  classical
  have hv' := hv
  have hmem := extremePoints_convexHull_subset hv
  obtain ⟨t, ht, rfl⟩ := hmem
  refine ⟨t, ht, rfl, ?_⟩
  intro s r hs hr hsr
  by_contra hne
  set d : ↥𝒩 → ℤ := fun g => r g - s g with hd
  let t1 : ↥𝒩 → ℕ := fun g => ((t g : ℤ) + d g).toNat
  let t2 : ↥𝒩 → ℕ := fun g => ((t g : ℤ) - d g).toNat
  have h1 : ∀ g, (t1 g : ℤ) = t g + d g := fun g => by
    have := hs g; have := hr g; simp only [t1, hd]; omega
  have h2 : ∀ g, (t2 g : ℤ) = t g - d g := fun g => by
    have := hs g; have := hr g; simp only [t2, hd]; omega
  have hsum : ∑ g : ↥𝒩, d g • (g : G) = 0 := by
    simp only [hd, sub_smul, Finset.sum_sub_distrib]; rw [hsr]; simp
  have hs1 : t1 ∈ groupSolutions 𝒩 g₀ := by
    unfold groupSolutions at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [← ht]
    have : ∀ g : ↥𝒩, t1 g • (g : G) = t g • (g : G) + d g • (g : G) := fun g => by
      rw [← natCast_zsmul, h1, add_smul, natCast_zsmul]
    simp only [this, Finset.sum_add_distrib, hsum, add_zero]
  have hs2 : t2 ∈ groupSolutions 𝒩 g₀ := by
    unfold groupSolutions at ht ⊢
    simp only [Set.mem_setOf_eq] at ht ⊢
    rw [← ht]
    have : ∀ g : ↥𝒩, t2 g • (g : G) = t g • (g : G) - d g • (g : G) := fun g => by
      rw [← natCast_zsmul, h2, sub_smul, natCast_zsmul]
    simp only [this, Finset.sum_sub_distrib, hsum, sub_zero]
  have hP1 : toReal 𝒩 t1 ∈ groupPolyhedron 𝒩 g₀ := subset_convexHull ℝ _ ⟨t1, hs1, rfl⟩
  have hP2 : toReal 𝒩 t2 ∈ groupPolyhedron 𝒩 g₀ := subset_convexHull ℝ _ ⟨t2, hs2, rfl⟩
  have hseg : toReal 𝒩 t ∈ openSegment ℝ (toReal 𝒩 t1) (toReal 𝒩 t2) := by
    refine ⟨1/2, 1/2, by norm_num, by norm_num, by norm_num, ?_⟩
    funext g
    have a := h1 g; have b := h2 g
    have a' : (t1 g : ℝ) = t g + d g := by exact_mod_cast a
    have b' : (t2 g : ℝ) = t g - d g := by exact_mod_cast b
    simp only [toReal, Pi.add_apply, Pi.smul_apply, smul_eq_mul, a', b']
    ring
  have := hv'.2 hP1 hP2 hseg
  apply hne
  funext g
  have := congrFun this g
  simp only [toReal] at this
  have a' : (t1 g : ℝ) = t g + d g := by exact_mod_cast h1 g
  have : (d g : ℝ) = 0 := by linarith
  have : d g = 0 := by exact_mod_cast this
  simp only [hd] at this; omega

end Gomory69.Asymptotic

open Gomory69.Asymptotic


theorem solution {G : Type*} [AddCommGroup G] [Fintype G] (𝒩 : Finset G)
    (h𝒩 : (0 : G) ∉ 𝒩) (t : ↥𝒩 → ℕ) (ht : IsIrreducible 𝒩 t) :
    ∏ g : ↥𝒩, (1 + t g) ≤ Fintype.card G := by
  exact thm1_core 𝒩 h𝒩 t ht
