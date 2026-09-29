-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.valuation_eq_exp_neg_count
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/5579bf6c-bb3f-58ad-83a1-88349d199c9d

import Mathlib.RingTheory.DedekindDomain.Factorization
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count

open scoped nonZeroDivisors

theorem solution {R : Type*} [CommRing R] [IsDedekindDomain R] (K : Type*) [Field K] [Algebra R K] [IsFractionRing R K] (v : IsDedekindDomain.HeightOneSpectrum R) {x : K} (hx : x ≠ 0) : v.valuation K x = WithZero.exp (-FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)) := by
  classical
  obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq R⁰ x
  have hr : r ≠ 0 := by
    rintro rfl
    exact hx (by simp)
  have hs : (s : R) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_mk',
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hr,
    IsDedekindDomain.HeightOneSpectrum.intValuation_if_neg _ hs]
  have hx' : FractionalIdeal.spanSingleton R⁰ (IsLocalization.mk' K r s) =
      ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) *
        ((Ideal.span {(s : R)} : Ideal R) : FractionalIdeal R⁰ K)⁻¹ := by
    rw [FractionalIdeal.coeIdeal_span_singleton, FractionalIdeal.coeIdeal_span_singleton,
      FractionalIdeal.spanSingleton_inv, FractionalIdeal.spanSingleton_mul_spanSingleton,
      IsFractionRing.mk'_eq_div, div_eq_mul_inv]
  have hr' : ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
  have hs' : ((Ideal.span {(s : R)} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rwa [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]
  rw [hx', FractionalIdeal.count_mul K v hr' (inv_ne_zero hs'), FractionalIdeal.count_inv,
    FractionalIdeal.count_coe K v (by rwa [Ne, Ideal.span_singleton_eq_bot] : Ideal.span {r} ≠ ⊥),
    FractionalIdeal.count_coe K v
      (by rwa [Ne, Ideal.span_singleton_eq_bot] : Ideal.span {(s : R)} ≠ ⊥),
    ← WithZero.exp_sub]
  congr 1
  ring

end S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_exp_neg_count (solution)
