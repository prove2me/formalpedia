-- Prove2me | solution 1 for ModularCurve.exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/0eb0d847-b2a9-5696-972a-d27e0f145104

import Mathlib
import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_CoeffSemilinearAut
import Theorems.Thm_ModularCurve_jqNModC_pow_eq_jqNModC_mul_of_charP
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow

set_option autoImplicit false

open ModularCurve

theorem solution
    (k₀ : Type) [Field k₀] (A₀ : ValuationSubring k₀)
    (q : ℕ) [Fact q.Prime] (hq𝔪 : ((q : ↥A₀)) ∈ IsLocalRing.maximalIdeal ↥A₀)
    (n : ℕ) [NeZero n] [NeZero (q * n)] :
    ∀ m : ℤ, ∃ a ∈ IsLocalRing.maximalIdeal ↥A₀,
      ((a : ↥A₀) : k₀) = (jqNModC k₀ (q * n) - (jqNModC k₀ n) ^ q).coeff m := by
  intro m

  set D : LaurentSeries ℤ := jqNModC ℤ (q * n) - (jqNModC ℤ n) ^ q with hD
  have hk₀ : jqNModC k₀ (q * n) - (jqNModC k₀ n) ^ q = coeffMap (Int.castRingHom k₀) D := by
    rw [hD, map_sub, map_pow, coeffSemilinearAut.coeffMap_jqNModC, coeffSemilinearAut.coeffMap_jqNModC]
  have hmod : coeffMap (Int.castRingHom (ZMod q)) D = 0 := by
    rw [hD, map_sub, map_pow, coeffSemilinearAut.coeffMap_jqNModC, coeffSemilinearAut.coeffMap_jqNModC,
      ModularCurve.jqNModC_pow_eq_jqNModC_mul_of_charP (ZMod q) q n, sub_self]
  have hdvd : (q : ℤ) ∣ D.coeff m := by
    have h := congrArg (fun x : LaurentSeries (ZMod q) => x.coeff m) hmod
    simp only [coeffMap_coeff] at h
    rw [HahnSeries.coeff_zero] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (D.coeff m) q).mp h
  obtain ⟨k, hk⟩ := hdvd
  refine ⟨(q : ↥A₀) * (k : ↥A₀), Ideal.mul_mem_right _ _ hq𝔪, ?_⟩
  rw [hk₀, coeffMap_coeff, hk, map_mul, map_natCast, eq_intCast]
  simp

end S_ModularCurve_exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow
end P2MW
export P2MW.S_ModularCurve_exists_mem_maximalIdeal_eq_coeff_jqNModC_mul_sub_pow (solution)
