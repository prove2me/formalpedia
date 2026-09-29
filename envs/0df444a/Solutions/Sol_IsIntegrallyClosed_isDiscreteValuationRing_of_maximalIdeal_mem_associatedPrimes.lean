-- Prove2me | solution 1 for IsIntegrallyClosed.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/53bb285a-f1ae-50eb-a9f5-06632dbfaf91

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes

open IsLocalRing

namespace Ws10Flat

section Local

variable {B : Type*} [CommRing B]

theorem exists_maximalIdeal_eq_colon_of_eq_radical_colon [IsNoetherianRing B] [IsLocalRing B]
    {I : Ideal B} {y : B} (h : maximalIdeal B = (I.colon {y}).radical) :
    ∃ y' : B, maximalIdeal B = I.colon {y'} := by
  classical
  obtain ⟨n, hn⟩ : ∃ n : ℕ, maximalIdeal B ^ n ≤ I.colon {y} :=
    Ideal.exists_pow_le_of_le_radical_of_fg h.le (IsNoetherian.noetherian _)
  have hex : ∃ k : ℕ, maximalIdeal B ^ k ≤ I.colon {y} := ⟨n, hn⟩
  set k := Nat.find hex with hk_def
  have hk : maximalIdeal B ^ k ≤ I.colon {y} := Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro hk0
    rw [hk0, pow_zero, Ideal.one_eq_top, top_le_iff] at hk

    rw [hk, Ideal.radical_top] at h
    exact (maximalIdeal.isMaximal B).ne_top h
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk0
  have hlt : ¬ maximalIdeal B ^ j ≤ I.colon {y} := Nat.find_min hex (by omega)
  obtain ⟨s, hs, hsy⟩ : ∃ s ∈ maximalIdeal B ^ j, s ∉ I.colon {y} := SetLike.not_le_iff_exists.mp hlt
  refine ⟨s * y, le_antisymm ?_ ?_⟩
  · intro m hm
    rw [Submodule.mem_colon_singleton, smul_eq_mul, ← mul_assoc]
    have : m * s ∈ maximalIdeal B ^ k := by
      rw [hj, pow_succ']
      exact Ideal.mul_mem_mul hm hs
    simpa [Submodule.mem_colon_singleton] using hk this
  · refine IsLocalRing.le_maximalIdeal fun htop => hsy ?_
    have h1 : (1 : B) ∈ I.colon {s * y} := by rw [htop]; trivial
    simpa [Submodule.mem_colon_singleton] using h1

theorem colon_bot_quotient_mk_eq (I : Ideal B) (y : B) :
    (⊥ : Submodule B (B ⧸ I)).colon {Ideal.Quotient.mk I y} = I.colon {y} := by
  ext r
  have hr : r • Ideal.Quotient.mk I y = Ideal.Quotient.mk I (r * y) := by
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, map_mul]
  rw [Submodule.mem_colon_singleton, Submodule.mem_colon_singleton, Submodule.mem_bot, hr,
    Ideal.Quotient.eq_zero_iff_mem, smul_eq_mul]

variable [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [IsLocalRing B]

theorem isDiscreteValuationRing_of_maximalIdeal_eq_colon
    {x y : B} (hx : x ≠ 0) (h : maximalIdeal B = (Ideal.span {x}).colon {y}) :
    IsDiscreteValuationRing B := by
  classical
  have h' : ∀ b : B, b ∈ maximalIdeal B ↔ b * y ∈ Ideal.span {x} := fun b => by
    rw [h, Submodule.mem_colon_singleton, smul_eq_mul]
  have h1 : (1 : B) ∉ maximalIdeal B := fun h1 =>
    (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  have hy : y ∉ Ideal.span {x} := fun hy => h1 ((h' 1).mpr (by simpa using hy))
  have hy0 : y ≠ 0 := by rintro rfl; exact hy (Ideal.zero_mem _)

  have key : ∀ m : B, m ∈ maximalIdeal B → ∃ b : B, m * y = x * b := fun m hm => by
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton'.mp ((h' m).mp hm)
    exact ⟨b, by rw [← hb, mul_comm]⟩
  choose! b hb using key

  have hnf : ¬ IsField B := by
    intro hF
    apply hy
    obtain ⟨xi, hxi⟩ := hF.mul_inv_cancel hx
    exact Ideal.mem_span_singleton'.mpr ⟨y * xi, by rw [mul_assoc, mul_comm xi x, hxi, mul_one]⟩
  by_cases hcase : ∃ m ∈ maximalIdeal B, b m ∉ maximalIdeal B
  ·
    obtain ⟨m, hm, hbm⟩ := hcase
    have hu : IsUnit (b m) := by
      by_contra hu; exact hbm ((IsLocalRing.mem_maximalIdeal _).mpr hu)
    obtain ⟨u, hu'⟩ := hu
    set n : B := m * ↑u⁻¹ with hn_def
    have hxn : x = y * n := by
      have e := hb m hm
      rw [← hu'] at e
      calc x = x * ↑u * ↑u⁻¹ := by simp
        _ = m * y * ↑u⁻¹ := by rw [e]
        _ = y * n := by ring
    have hn : n ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hm
    have hprinc : (maximalIdeal B).IsPrincipal := by
      refine ⟨⟨n, le_antisymm ?_ ?_⟩⟩
      · intro m' hm'
        have e := hb m' hm'
        rw [hxn] at e
        have : m' = n * b m' := by
          have e' : y * m' = y * (n * b m') := by rw [mul_comm y m', e]; ring
          exact mul_left_cancel₀ hy0 e'
        rw [this]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self n)
      · rw [Ideal.submodule_span_eq, Ideal.span_singleton_le_iff_mem]
        exact hn
    exact ((IsDiscreteValuationRing.TFAE B hnf).out 0 4).mpr hprinc
  ·
    push Not at hcase
    exfalso
    let K := FractionRing B
    have hinj : Function.Injective (algebraMap B K) := IsFractionRing.injective B K
    have hxK : algebraMap B K x ≠ 0 := fun e => hx (hinj (by rw [e, map_zero]))
    let z : K := algebraMap B K y / algebraMap B K x
    let N : Submodule B K := IsLocalization.coeSubmodule K (maximalIdeal B)
    have hNfg : N.FG := Submodule.FG.map _ (IsNoetherian.noetherian _)
    have hNne : N ≠ ⊥ := by
      intro hN
      have : maximalIdeal B = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr fun m hm => ?_
        have hmN : algebraMap B K m ∈ N := ⟨m, hm, rfl⟩
        rw [hN, Submodule.mem_bot] at hmN
        exact hinj (by rw [hmN, map_zero])
      exact hnf (IsLocalRing.isField_iff_maximalIdeal_eq.mpr this)
    have hz : ∀ v ∈ N, z • v ∈ N := by
      rintro _ ⟨m, hm, rfl⟩
      refine ⟨b m, hcase m hm, ?_⟩
      have e := hb m hm
      change algebraMap B K (b m) = z • algebraMap B K m
      rw [smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hxK, ← map_mul, ← map_mul]
      congr 1
      rw [mul_comm (b m) x, ← e, mul_comm]
    have hzint : IsIntegral B z := isIntegral_of_smul_mem_submodule N hNne hNfg z hz
    obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.mp hzint
    apply hy
    refine Ideal.mem_span_singleton'.mpr ⟨c, hinj ?_⟩
    rw [map_mul, hc, div_mul_cancel₀ _ hxK]

theorem isDiscreteValuationRing_of_maximalIdeal_eq_radical_colon
    {x y : B} (hx : x ≠ 0) (h : maximalIdeal B = ((Ideal.span {x}).colon {y}).radical) :
    IsDiscreteValuationRing B := by
  obtain ⟨y', hy'⟩ := exists_maximalIdeal_eq_colon_of_eq_radical_colon h
  exact isDiscreteValuationRing_of_maximalIdeal_eq_colon hx hy'

theorem isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
    {x : B} (hx : x ≠ 0) (h : maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing B := by
  have h' : IsAssociatedPrime (maximalIdeal B) (B ⧸ Ideal.span {x}) := h
  obtain ⟨z, hz⟩ := h'.eq_radical_colon
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine isDiscreteValuationRing_of_maximalIdeal_eq_radical_colon hx (y := y) ?_
  rw [hz, colon_bot_quotient_mk_eq]

end Local

end Ws10Flat

theorem solution
    {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B] [IsIntegrallyClosed B] [IsLocalRing B]
    {x : B} (hx : x ≠ 0)
    (h : IsLocalRing.maximalIdeal B ∈ associatedPrimes B (B ⧸ Ideal.span {x})) :
    IsDiscreteValuationRing B :=
  Ws10Flat.isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes hx h

end S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes
end P2MW
export P2MW.S_IsIntegrallyClosed_isDiscreteValuationRing_of_maximalIdeal_mem_associatedPrimes (solution)
