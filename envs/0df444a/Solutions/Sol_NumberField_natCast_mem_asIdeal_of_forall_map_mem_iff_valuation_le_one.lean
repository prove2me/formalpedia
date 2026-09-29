-- Prove2me | solution 1 for NumberField.natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/891b2ba9-5cc7-5bdd-ba94-3eacf755423b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one

set_option autoImplicit false
set_option maxHeartbeats 1600000

open NumberField IsDedekindDomain

theorem solution
    (K : Type) [Field K] [NumberField K] {Ω : Type} [Field Ω]
    (σ : K →+* Ω) (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K))
    (hv : ∀ x : K, σ x ∈ A ↔ v.valuation K x ≤ 1)
    (p : ℕ) (hp : A.valuation (σ (p : K)) < 1) :
    ((p : ℤ) : 𝓞 K) ∈ v.asIdeal := by

  have hcast : algebraMap (𝓞 K) K ((p : ℤ) : 𝓞 K) = (p : K) := by
    rw [map_intCast, Int.cast_natCast]
  by_cases hp0 : (p : K) = 0
  ·
    have : ((p : ℤ) : 𝓞 K) = 0 :=
      (map_eq_zero_iff (algebraMap (𝓞 K) K) (IsFractionRing.injective (𝓞 K) K)).mp
        (hcast.trans hp0)
    rw [this]
    exact Ideal.zero_mem _

  have hσp0 : σ (p : K) ≠ 0 := (map_ne_zero σ).mpr hp0
  have hnot : σ ((p : K)⁻¹) ∉ A := by
    intro hmem
    rw [map_inv₀, ← A.valuation_le_one_iff, map_inv₀,
      inv_le_one₀ (zero_lt_iff.mpr ((Valuation.ne_zero_iff _).mpr hσp0))] at hmem
    exact absurd hp (not_lt.mpr hmem)
  rw [hv, not_le, ← hcast, map_inv₀] at hnot

  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := K)]
  have hne : v.valuation K (algebraMap (𝓞 K) K ((p : ℤ) : 𝓞 K)) ≠ 0 := by
    rw [Valuation.ne_zero_iff, hcast]
    exact hp0
  exact (one_lt_inv₀ (zero_lt_iff.mpr hne)).mp hnot

end S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one
end P2MW
export P2MW.S_NumberField_natCast_mem_asIdeal_of_forall_map_mem_iff_valuation_le_one (solution)
