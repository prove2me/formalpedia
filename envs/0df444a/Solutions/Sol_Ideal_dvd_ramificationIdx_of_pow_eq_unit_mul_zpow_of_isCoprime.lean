-- Prove2me | solution 1 for Ideal.dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5dd89c48-8de0-5f43-8ec4-1fb4f3dddb94

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime

set_option autoImplicit false
set_option maxHeartbeats 800000

open IsDedekindDomain in
theorem solution
    {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra O R]
    {E : Type*} [Field E] [Algebra R E] [IsFractionRing R E] [Algebra O E] [IsScalarTower O R E]
    (ϖ : O) (hϖ : Irreducible ϖ) (u : Oˣ) (m : ℤ) (n : ℕ) (hn : 0 < n) (hmn : IsCoprime m (n : ℤ))
    (a : E) (hab : a ^ n = algebraMap O E (u : O) * algebraMap O E ϖ ^ m)
    (𝔓 : Ideal R) [𝔓.IsPrime] (h𝔓 : 𝔓 ≠ ⊥) [𝔓.LiesOver (IsLocalRing.maximalIdeal O)] :
    n ∣ (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 := by
  classical
  have hmap : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) = Ideal.span {algebraMap O R ϖ} := by
    rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]
  by_cases hϖR : algebraMap O R ϖ = 0
  ·
    have hbot : Ideal.map (algebraMap O R) (IsLocalRing.maximalIdeal O) = ⊥ := by
      rw [hmap, Ideal.span_singleton_eq_bot]
      exact hϖR
    have h0 : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = 0 :=
      Ideal.ramificationIdx_eq_zero fun k => ⟨k + 1, by rw [hbot]; exact bot_le, Nat.lt_succ_self k⟩
    rw [h0]
    exact dvd_zero n

  let v : HeightOneSpectrum R := ⟨𝔓, inferInstance, h𝔓⟩
  let val := HeightOneSpectrum.valuation E v
  have hne : v.intValuation (algebraMap O R ϖ) ≠ 0 := HeightOneSpectrum.intValuation_ne_zero v _ hϖR
  obtain ⟨k, hk⟩ : ∃ k : ℤ, v.intValuation (algebraMap O R ϖ) = WithZero.exp k := ⟨_, (WithZero.exp_log hne).symm⟩
  have hk0 : k ≤ 0 := by
    have h1 := HeightOneSpectrum.intValuation_le_one v (algebraMap O R ϖ)
    rw [hk, ← WithZero.exp_zero, WithZero.exp_le_exp] at h1
    exact h1
  obtain ⟨t, rfl⟩ : ∃ t : ℕ, k = -(t : ℤ) := ⟨(-k).toNat, by omega⟩

  have he : (IsLocalRing.maximalIdeal O).ramificationIdx' 𝔓 = t := by
    apply Ideal.ramificationIdx_spec
    · rw [hmap]
      exact Ideal.dvd_iff_le.mp ((v.intValuation_le_pow_iff_dvd _ t).mp (le_of_eq hk))
    · rw [hmap]
      intro hle
      have h2 := (v.intValuation_le_pow_iff_dvd _ (t + 1)).mpr (Ideal.dvd_iff_le.mpr hle)
      rw [hk, WithZero.exp_le_exp] at h2
      omega

  have hvϖ : val (algebraMap O E ϖ) = WithZero.exp (-(t : ℤ)) := by
    rw [IsScalarTower.algebraMap_apply O R E, HeightOneSpectrum.valuation_of_algebraMap, hk]
  have hvu : val (algebraMap O E (u : O)) = 1 := by
    rw [IsScalarTower.algebraMap_apply O R E, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.intValuation_eq_one_iff]
    intro hmem
    have hu𝔪 : (u : O) ∈ IsLocalRing.maximalIdeal O := (Ideal.mem_of_liesOver 𝔓 _ (u : O)).mpr hmem
    exact (IsLocalRing.mem_maximalIdeal _).mp hu𝔪 u.isUnit

  have hva : val a ^ n = WithZero.exp (-(t : ℤ)) ^ m := by
    have h := congrArg val hab
    rwa [map_pow, map_mul, map_zpow₀, hvu, one_mul, hvϖ] at h
  have ha0 : val a ≠ 0 := by
    intro h0
    rw [h0, zero_pow hn.ne', ← WithZero.exp_zsmul] at hva
    exact WithZero.exp_ne_zero hva.symm
  obtain ⟨ka, hka⟩ : ∃ ka : ℤ, val a = WithZero.exp ka := ⟨_, (WithZero.exp_log ha0).symm⟩
  rw [hka, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, WithZero.exp_inj, nsmul_eq_mul, smul_eq_mul] at hva

  have hdvd : (n : ℤ) ∣ m * (t : ℤ) := ⟨-ka, by linarith⟩
  have hnt : (n : ℤ) ∣ (t : ℤ) := hmn.symm.dvd_of_dvd_mul_left hdvd
  rw [he]
  exact Int.natCast_dvd_natCast.mp hnt

end S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime
end P2MW
export P2MW.S_Ideal_dvd_ramificationIdx_of_pow_eq_unit_mul_zpow_of_isCoprime (solution)
