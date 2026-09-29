-- Prove2me | solution 1 for IsIntegrallyClosed.exists_algebraMap_eq_of_forall_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/66e98984-318c-5262-80b5-93dc66d2b681

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (x : K)
    (hx : ∀ (p : Ideal R) [p.IsPrime], p.height = 1 →
      ∃ r s : R, s ∉ p ∧ x * algebraMap R K s = algebraMap R K r) :
    ∃ r : R, algebraMap R K r = x := by
  classical
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap R K b ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hb0
  by_cases hab : b ∣ a
  · obtain ⟨d, rfl⟩ := hab
    exact ⟨d, by rw [map_mul, mul_div_cancel_left₀ _ hbK]⟩
  exfalso

  have ha : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  obtain ⟨p, hp, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ ha
  haveI := hp.isPrime

  have h1 : p.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 p hp
  obtain ⟨r, s, hs, hrs⟩ := hx p h1

  have hsa : s * a = b * r := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_mul, ← hrs]
    field_simp

  refine hs (hle ?_)
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def,
    Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem,
    Ideal.mem_span_singleton]
  exact ⟨r, hsa⟩

end S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one
end P2MW
export P2MW.S_IsIntegrallyClosed_exists_algebraMap_eq_of_forall_height_eq_one (solution)
