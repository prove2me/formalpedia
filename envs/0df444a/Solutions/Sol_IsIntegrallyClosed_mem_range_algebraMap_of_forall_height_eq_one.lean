-- Prove2me | solution 1 for IsIntegrallyClosed.mem_range_algebraMap_of_forall_height_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/e08db0fa-6dd8-5a3c-9e18-f3f2e0a43099

import Mathlib
import Theorems.Thm_IsIntegrallyClosed_height_eq_one_of_mem_associatedPrimes
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
set_option autoImplicit false

theorem solution
    {R : Type*} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    (x : K)
    (hx : ∀ P : Ideal R, P.IsPrime → P.height = 1 →
      ∃ a s : R, s ∉ P ∧ x * algebraMap R K s = algebraMap R K a) :
    x ∈ Set.range (algebraMap R K) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hbK : algebraMap R K b ≠ 0 := (map_ne_zero_iff _ hinj).mpr hb0
  by_contra hnot

  have ha : a ∉ Ideal.span {b} := by
    intro hmem
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hmem
    exact hnot ⟨c, by rw [← hc, map_mul, mul_div_assoc, div_self hbK, mul_one]⟩

  have hcls : Ideal.Quotient.mk (Ideal.span {b}) a ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  obtain ⟨P, hP, hle⟩ := exists_le_isAssociatedPrime_of_isNoetherianRing R _ hcls
  haveI := hP.isPrime
  have hP1 : P.height = 1 := IsIntegrallyClosed.height_eq_one_of_mem_associatedPrimes hb0 P hP
  obtain ⟨a', s, hs, hxs⟩ := hx P hP.isPrime hP1
  apply hs
  apply hle
  rw [Submodule.mem_colon_singleton, Submodule.mem_bot, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]

  have hK : algebraMap R K (s * a) = algebraMap R K (a' * b) := by
    rw [map_mul, map_mul, ← hxs]
    field_simp
  have hR : s * a = a' * b := hinj hK
  exact Ideal.mem_span_singleton'.mpr ⟨a', hR.symm⟩

end S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one
end P2MW
export P2MW.S_IsIntegrallyClosed_mem_range_algebraMap_of_forall_height_eq_one (solution)
