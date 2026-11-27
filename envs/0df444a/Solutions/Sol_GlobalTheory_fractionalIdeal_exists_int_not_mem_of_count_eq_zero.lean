-- Prove2me | solution 1 for GlobalTheory.fractionalIdeal_exists_int_not_mem_of_count_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:39:38.176638+00:00
-- url     : https://prove2.me/submissions/54d1b44a-caa3-48b1-a510-ebd6e23ae5c3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FractionalIdealExistsIntNotMemOfCountEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain
open GlobalTheory
namespace GlobalTheory
theorem _root_.solution
    {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    (v : HeightOneSpectrum R) (I : FractionalIdeal (nonZeroDivisors R) K) :
    I ≠ 0 → FractionalIdeal.count K v I = 0 → ∃ s : R, s ∉ v.asIdeal ∧ algebraMap R K s ∈ I := by
  intro hI hc
  classical
  obtain ⟨a, J, ha, haJ⟩ := FractionalIdeal.exists_eq_spanSingleton_mul I
  have hJ : J ≠ 0 := by
    rintro rfl
    apply hI
    rw [haJ]
    simp
  have hv : Irreducible (Associates.mk v.asIdeal) := v.associates_irreducible
  rw [FractionalIdeal.count_well_defined K v hI haJ, sub_eq_zero, Nat.cast_inj] at hc
  set n := (Associates.mk v.asIdeal).count (Associates.mk J).factors with hn
  have hJne : Associates.mk J ≠ 0 := Associates.mk_ne_zero.mpr hJ
  have haspan : Ideal.span {a} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ha
  have haNe : Associates.mk (Ideal.span {a}) ≠ 0 := Associates.mk_ne_zero.mpr haspan
  have hdJ : v.asIdeal ^ n ∣ J := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le hJne hv).mpr le_rfl
  have hda : v.asIdeal ^ n ∣ Ideal.span {a} := by
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow]
    exact (Associates.prime_pow_dvd_iff_le haNe hv).mpr hc.le
  obtain ⟨J1, hJ1⟩ := hdJ
  have hnot : ¬ v.asIdeal ∣ J1 := by
    intro h
    have h2 : v.asIdeal ^ (n + 1) ∣ J := by
      rw [hJ1, pow_succ]
      exact mul_dvd_mul_left _ h
    rw [← Associates.mk_le_mk_iff_dvd, Associates.mk_pow,
      Associates.prime_pow_dvd_iff_le hJne hv] at h2
    omega
  rw [Ideal.dvd_iff_le, SetLike.not_le_iff_exists] at hnot
  obtain ⟨s, hsJ1, hsv⟩ := hnot
  refine ⟨s, hsv, ?_⟩
  have hsa : s * a ∈ J := by
    rw [hJ1, mul_comm s a]
    exact Ideal.mul_mem_mul (Ideal.dvd_iff_le.mp hda (Ideal.mem_span_singleton_self a)) hsJ1
  rw [haJ, FractionalIdeal.mem_singleton_mul]
  refine ⟨algebraMap R K (s * a), FractionalIdeal.mem_coeIdeal_of_mem _ hsa, ?_⟩
  have ha' : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr ha
  rw [map_mul]
  field_simp
end GlobalTheory
