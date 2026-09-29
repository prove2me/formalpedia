-- Prove2me | solution 1 for Ideal.mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/d6ddb7c1-dc7f-5797-967f-b26c55f7f7fc

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal

set_option autoImplicit false

open IsLocalRing

universe u

theorem solution
    {A : Type u} [CommRing A] (𝔪 : Ideal A) [𝔪.IsMaximal]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B] [IsLocalization.AtPrime B 𝔪]
    (h : 𝔪 ≤ (maximalIdeal B).comap (Algebra.ofId A B)) :
    Function.Bijective (Ideal.mapCotangent 𝔪 (maximalIdeal B) (Algebra.ofId A B) h) := by
  classical

  have h' : ∀ x ∈ 𝔪, algebraMap A B x ∈ maximalIdeal B := fun x hx => h hx

  have hmap : maximalIdeal B = Ideal.map (algebraMap A B) 𝔪 := by
    refine le_antisymm ?_ (Ideal.map_le_iff_le_comap.mpr fun x hx => h' x hx)
    intro y hy
    obtain ⟨⟨x, s⟩, rfl⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl y
    dsimp only at hy ⊢
    have hx : x ∈ 𝔪 := (IsLocalization.AtPrime.mk'_mem_maximal_iff B 𝔪 x s).mp hy
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ hx)
  have hmap2 : maximalIdeal B ^ 2 = Ideal.map (algebraMap A B) (𝔪 ^ 2) := by
    rw [Ideal.map_pow, hmap]
  have hsq : ∀ w ∈ 𝔪 ^ 2, algebraMap A B w ∈ maximalIdeal B ^ 2 := fun w hw => by
    rw [hmap2]; exact Ideal.mem_map_of_mem _ hw
  constructor
  ·
    intro v₁ v₂ hv
    obtain ⟨x₁, rfl⟩ := Ideal.toCotangent_surjective 𝔪 v₁
    obtain ⟨x₂, rfl⟩ := Ideal.toCotangent_surjective 𝔪 v₂
    rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq] at hv
    rw [Ideal.toCotangent_eq]

    set x : A := (x₁ : A) - (x₂ : A) with hxdef
    have hxm : x ∈ 𝔪 := 𝔪.sub_mem x₁.2 x₂.2
    have hv' : algebraMap A B x ∈ Ideal.map (algebraMap A B) (𝔪 ^ 2) := by
      rw [← hmap2]
      simpa [hxdef, map_sub] using hv
    obtain ⟨⟨i, s⟩, e⟩ := (IsLocalization.mem_map_algebraMap_iff 𝔪.primeCompl B).mp hv'

    have e' : algebraMap A B (x * (s : A)) = algebraMap A B (i : A) := by rw [map_mul]; exact e
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists 𝔪.primeCompl B).mp e'

    have hu : (c : A) * (s : A) ∉ 𝔪 := (𝔪.primeCompl.mul_mem c.2 s.2)
    have hux : ((c : A) * (s : A)) * x ∈ 𝔪 ^ 2 := by
      have : ((c : A) * (s : A)) * x = (c : A) * (i : A) := by rw [← hc]; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ i.2
    obtain ⟨b, c', hc', hbc⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› hu
    have : x = b * (((c : A) * (s : A)) * x) + x * c' := by
      have := hbc
      linear_combination (-x) * this
    rw [this]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ hux) ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul hxm hc'
  ·
    intro w
    obtain ⟨y, rfl⟩ := Ideal.toCotangent_surjective _ w
    obtain ⟨⟨x, s⟩, hy⟩ := IsLocalization.mk'_surjective 𝔪.primeCompl (y : B)
    dsimp only at hy
    have hx : x ∈ 𝔪 := by
      rw [← IsLocalization.AtPrime.mk'_mem_maximal_iff B 𝔪 x s, hy]; exact y.2
    obtain ⟨b, c', hc', hbc⟩ := Ideal.IsMaximal.exists_inv ‹𝔪.IsMaximal› (show (s : A) ∉ 𝔪 from s.2)
    refine ⟨Ideal.toCotangent 𝔪 ⟨b * x, 𝔪.mul_mem_left b hx⟩, ?_⟩
    rw [Ideal.mapCotangent_toCotangent, Ideal.toCotangent_eq]

    have hunit : IsUnit (algebraMap A B (s : A)) := IsLocalization.map_units B s
    obtain ⟨u, hu⟩ := hunit
    have hspec : (y : B) * algebraMap A B (s : A) = algebraMap A B x := by
      rw [← hy]; exact IsLocalization.mk'_spec B x s
    have key : algebraMap A B (s : A) * (algebraMap A B (b * x) - (y : B)) = -algebraMap A B (x * c') := by
      have : (y : B) * algebraMap A B (s : A) = algebraMap A B x := hspec
      have hbc' := congrArg (algebraMap A B) hbc
      simp only [map_add, map_mul, map_one] at hbc'
      rw [map_mul, map_mul]
      linear_combination (algebraMap A B x) * hbc' - this
    have hmem : algebraMap A B (s : A) * (algebraMap A B (b * x) - (y : B)) ∈ maximalIdeal B ^ 2 := by
      rw [key]
      refine neg_mem_iff.mpr (hsq _ ?_)
      rw [pow_two]; exact Ideal.mul_mem_mul hx hc'
    have : (algebraMap A B (b * x) - (y : B)) = ↑u⁻¹ * (algebraMap A B (s : A) * (algebraMap A B (b * x) - (y : B))) := by
      rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
    show (algebraMap A B (b * x) - (y : B)) ∈ maximalIdeal B ^ 2
    rw [this]
    exact Ideal.mul_mem_left _ _ hmem

end S_Ideal_mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal
end P2MW
export P2MW.S_Ideal_mapCotangent_bijective_of_isLocalization_atPrime_of_isMaximal (solution)
