-- Prove2me | solution 1 for HenselianLocalRing.isLocalRing_of_isDomain_of_moduleFinite
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/59f89764-a160-56f1-8189-3789f745e4bc

import Mathlib
import Theorems.Thm_HenselianLocalRing_existsUnique_isIdempotentElem_mk_eq_of_moduleFinite
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite

set_option autoImplicit false
set_option maxHeartbeats 1600000

universe u v

namespace S17Hens

theorem isArtinianRing_quotient_map_maximalIdeal
    {R : Type u} [CommRing R] [IsLocalRing R]
    {S : Type v} [CommRing S] [Algebra R S] [Module.Finite R S] :
    IsArtinianRing (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S)) := by
  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  let k := R ⧸ IsLocalRing.maximalIdeal R
  letI : Field k := Ideal.Quotient.field _
  have hJR : ∀ r ∈ IsLocalRing.maximalIdeal R, algebraMap R (S ⧸ J) r = 0 := by
    intro r hr
    rw [IsScalarTower.algebraMap_apply R S (S ⧸ J), Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_map_of_mem _ hr
  letI : Algebra k (S ⧸ J) := (Ideal.Quotient.lift _ (algebraMap R (S ⧸ J)) hJR).toAlgebra
  haveI : IsScalarTower R k (S ⧸ J) := IsScalarTower.of_algebraMap_eq (fun r => rfl)
  haveI : Module.Finite k (S ⧸ J) := Module.Finite.of_restrictScalars_finite R k (S ⧸ J)
  exact IsArtinianRing.of_finite k (S ⧸ J)

theorem isLocalRing_of_isDomain_of_moduleFinite
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S := by
  classical
  by_contra hS

  have h1 : ∃ a : S, ¬ IsUnit a ∧ ¬ IsUnit (1 - a) := by
    by_contra h
    push Not at h
    exact hS (IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => by
      by_cases ha : IsUnit a
      · exact Or.inl ha
      · exact Or.inr (h a ha))
  obtain ⟨a, ha, ha'⟩ := h1
  obtain ⟨m₁, hm₁, ham₁⟩ := exists_max_ideal_of_mem_nonunits ha
  obtain ⟨m₂, hm₂, ham₂⟩ := exists_max_ideal_of_mem_nonunits ha'
  have hne : m₁ ≠ m₂ := by
    intro h
    subst h
    have : (1 : S) ∈ m₁ := by
      have := m₁.add_mem ham₁ ham₂
      rwa [add_sub_cancel] at this
    exact hm₁.ne_top ((Ideal.eq_top_iff_one _).mpr this)

  set J : Ideal S := (IsLocalRing.maximalIdeal R).map (algebraMap R S) with hJ
  have hJle : ∀ m : Ideal S, m.IsMaximal → J ≤ m := by
    intro m hm
    rw [hJ, Ideal.map_le_iff_le_comap]
    haveI := hm
    have hmax : (m.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal m
    rw [IsLocalRing.eq_maximalIdeal hmax]

  haveI : IsArtinianRing (S ⧸ J) := isArtinianRing_quotient_map_maximalIdeal
  have hsurj : Function.Surjective (Ideal.Quotient.mk J) := Ideal.Quotient.mk_surjective
  have hmaxq : ∀ m : Ideal S, m.IsMaximal → (m.map (Ideal.Quotient.mk J)).IsMaximal := by
    intro m hm
    rcases Ideal.map_eq_top_or_isMaximal_of_surjective _ hsurj hm with h | h
    · exfalso
      have : m = ⊤ := by
        have h2 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h
        rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_top] at h2
        have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
          rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
        rw [hker, sup_eq_left.mpr (hJle m hm)] at h2
        exact h2
      exact hm.ne_top this
    · exact h
  let M₁ : MaximalSpectrum (S ⧸ J) := ⟨m₁.map (Ideal.Quotient.mk J), hmaxq m₁ hm₁⟩
  let M₂ : MaximalSpectrum (S ⧸ J) := ⟨m₂.map (Ideal.Quotient.mk J), hmaxq m₂ hm₂⟩
  have hM : M₁ ≠ M₂ := by
    intro h
    apply hne
    have h2 : m₁.map (Ideal.Quotient.mk J) = m₂.map (Ideal.Quotient.mk J) := congrArg MaximalSpectrum.asIdeal h
    have h3 := congrArg (Ideal.comap (Ideal.Quotient.mk J)) h2
    rw [Ideal.comap_map_of_surjective _ hsurj, Ideal.comap_map_of_surjective _ hsurj] at h3
    have hker : Ideal.comap (Ideal.Quotient.mk J) ⊥ = J := by
      rw [← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    rwa [hker, sup_eq_left.mpr (hJle m₁ hm₁), sup_eq_left.mpr (hJle m₂ hm₂)] at h3

  let π := IsArtinianRing.quotNilradicalEquivPi (S ⧸ J)
  let f₀ : ∀ I : MaximalSpectrum (S ⧸ J), (S ⧸ J) ⧸ I.asIdeal := Pi.single M₁ 1
  have hf₀ : IsIdempotentElem f₀ := by
    show f₀ * f₀ = f₀
    ext I
    by_cases hI : I = M₁
    · subst hI; simp [f₀]
    · simp [f₀, hI]
  have hf₀0 : f₀ ≠ 0 := by
    intro h
    have := congrFun h M₁
    simp [f₀] at this
    exact M₁.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this.symm)
  have hf₀1 : f₀ ≠ 1 := by
    intro h
    have := congrFun h M₂
    have h0 : f₀ M₂ = 0 := Pi.single_eq_of_ne hM.symm _
    rw [h0, Pi.one_apply] at this
    exact M₂.isMaximal.ne_top (Ideal.Quotient.zero_eq_one_iff.mp this)
  let ē₀ := π.symm f₀
  have hē₀ : IsIdempotentElem ē₀ := by
    show π.symm f₀ * π.symm f₀ = π.symm f₀
    rw [← map_mul, hf₀.eq]

  have hnil : ∀ y ∈ RingHom.ker (Ideal.Quotient.mk (nilradical (S ⧸ J))), IsNilpotent y := by
    intro y hy
    rw [Ideal.mk_ker] at hy
    exact hy
  obtain ⟨ē, hē, hēē₀⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (Ideal.Quotient.mk (nilradical (S ⧸ J))) hnil ē₀
    (Ideal.Quotient.mk_surjective ē₀) hē₀

  obtain ⟨e, ⟨he, hemk⟩, -⟩ := HenselianLocalRing.existsUnique_isIdempotentElem_mk_eq_of_moduleFinite ē hē

  rcases IsIdempotentElem.iff_eq_zero_or_one.mp he with h0 | h1
  · apply hf₀0
    have : ē = 0 := by rw [← hemk, h0, map_zero]
    have : ē₀ = 0 := by rw [← hēē₀, this, map_zero]
    have : f₀ = π 0 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_zero]
  · apply hf₀1
    have : ē = 1 := by rw [← hemk, h1, map_one]
    have : ē₀ = 1 := by rw [← hēē₀, this, map_one]
    have : f₀ = π 1 := by rw [← this]; exact (π.apply_symm_apply f₀).symm
    rw [this, map_one]

end S17Hens

theorem solution
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsDomain S] [Algebra R S] [Module.Finite R S] : IsLocalRing S :=
  S17Hens.isLocalRing_of_isDomain_of_moduleFinite (R := R)

end S_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite
end P2MW
export P2MW.S_HenselianLocalRing_isLocalRing_of_isDomain_of_moduleFinite (solution)
