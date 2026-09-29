-- Prove2me | solution 1 for IsDedekindDomain.exists_zpow_mul_div_of_ramificationIdx_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/11c2f38e-657e-57ad-b527-796fa1058095

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one

set_option autoImplicit false

universe u

open scoped Pointwise

open IsDedekindDomain WithZero

theorem solution
    {A : Type u} {B : Type u} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDedekindDomain B]
    [Algebra A B] (π : A) (p : Ideal A) [p.IsMaximal] (hp : p = Ideal.span {π})
    (q : Ideal B) [q.IsMaximal] (hq : q ≠ ⊥) (hpq : Ideal.map (algebraMap A B) p ≤ q)
    (he : Ideal.ramificationIdx' p q = 1)
    (L : Type u) [Field L] [Algebra B L] [IsFractionRing B L] [Algebra A L] [IsScalarTower A B L]
    (z : L) (hz : z ≠ 0) :
    ∃ (n : ℤ) (b s : B), b ∉ q ∧ s ∉ q ∧
      z * (algebraMap B L s) = (algebraMap A L π) ^ n * algebraMap B L b := by
  classical

  let v : HeightOneSpectrum B := ⟨q, inferInstance, hq⟩
  have hv : v.asIdeal = q := rfl
  set πB : B := algebraMap A B π with hπB
  have hmap : Ideal.map (algebraMap A B) p = Ideal.span {πB} := by
    rw [hp, Ideal.map_span, Set.image_singleton]

  have hπB0 : πB ≠ 0 := by
    intro h0
    have hbot : Ideal.map (algebraMap A B) p = ⊥ := by rw [hmap, h0, Ideal.span_singleton_eq_bot]
    have : Ideal.ramificationIdx' p q = 0 :=
      Ideal.ramificationIdx_eq_zero (fun n => ⟨n + 1, by rw [hbot]; exact bot_le, Nat.lt_succ_self n⟩)
    omega
  have hmap0 : Ideal.map (algebraMap A B) p ≠ ⊥ := by
    rw [hmap, Ne, Ideal.span_singleton_eq_bot]; exact hπB0
  have hvπ : v.intValuation πB = exp (-1 : ℤ) := by
    rw [v.intValuation_eq_exp_neg_multiplicity hπB0, hv, ← hmap,
      ← Ideal.IsDedekindDomain.ramificationIdx'_eq_multiplicity hmap0 (inferInstance : q.IsPrime), he]
    rfl
  have hπL : algebraMap A L π = algebraMap B L πB := by
    rw [hπB, ← IsScalarTower.algebraMap_apply]
  have hwπ : v.valuation L (algebraMap A L π) = exp (-1 : ℤ) := by
    rw [hπL, HeightOneSpectrum.valuation_of_algebraMap, hvπ]
  have hπL0 : algebraMap A L π ≠ 0 := by
    rw [hπL]; exact (map_ne_zero_iff _ (IsFractionRing.injective B L)).mpr hπB0

  have hwz0 : v.valuation L z ≠ 0 := (Valuation.ne_zero_iff _).mpr hz
  set k : ℤ := log (v.valuation L z) with hk
  have hwz : v.valuation L z = exp k := by rw [hk, exp_log hwz0]

  set y : L := z * (algebraMap A L π) ^ k with hy
  have hwy : v.valuation L y = 1 := by
    rw [hy, map_mul, map_zpow₀, hwz, hwπ, ← exp_zsmul, ← exp_add]
    simp

  obtain ⟨b, ⟨s, hs⟩, hbs⟩ := HeightOneSpectrum.exists_primeCompl_mul_eq_of_integer v y hwy.le
  have hs' : s ∉ q := hs
  have hws : v.valuation L (algebraMap B L s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (v.intValuation_eq_one_iff_mem_primeCompl s).mpr hs
  have hb' : b ∉ q := by
    have hwb : v.valuation L (algebraMap B L b) = 1 := by rw [← hbs, map_mul, hwy, hws, one_mul]
    rw [HeightOneSpectrum.valuation_of_algebraMap] at hwb
    exact (v.intValuation_eq_one_iff_mem_primeCompl b).mp hwb
  refine ⟨-k, b, s, hb', hs', ?_⟩

  rw [← hbs, hy, zpow_neg]
  field_simp

end S_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one
end P2MW
export P2MW.S_IsDedekindDomain_exists_zpow_mul_div_of_ramificationIdx_eq_one (solution)
