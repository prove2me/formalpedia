-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.valuation_eq_ofAdd_neg_count_spanSingleton
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/a44d5f22-d9f8-5ed5-ba89-b1f4773bc608

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton
open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors
set_option autoImplicit false
set_option maxHeartbeats 4000000

theorem solution
    {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
    [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R) (x : K) (hx : x ≠ 0) :
    v.valuation K x =
      (↑(Multiplicative.ofAdd (-(FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ x)))) :
        WithZero (Multiplicative ℤ)) := by
  obtain ⟨⟨a, d⟩, hxd⟩ := IsLocalization.surj R⁰ x
  simp only at hxd
  have hd0 : (d : R) ≠ 0 := nonZeroDivisors.coe_ne_zero d
  have hdK : (algebraMap R K (d:R)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hd0
  have ha0 : a ≠ 0 := by
    rintro rfl; rw [map_zero] at hxd
    exact hx ((mul_eq_zero.mp hxd).resolve_right hdK)
  set na : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {a})).factors with hna
  set nd : ℕ := (Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(d:R)})).factors with hnd

  have hval : v.valuation K x * WithZero.exp (-(nd:ℤ)) = WithZero.exp (-(na:ℤ)) := by
    have hintValDef : ∀ r : R, r ≠ 0 →
        v.intValuation r = WithZero.exp (-(((Associates.mk v.asIdeal).count
          (Associates.mk (Ideal.span {r})).factors : ℕ) : ℤ)) := fun r hr => by
      rw [show v.intValuation r = v.intValuationDef r from rfl]
      exact v.intValuationDef_if_neg hr
    have := congrArg (v.valuation K) hxd
    rw [map_mul, v.valuation_of_algebraMap, v.valuation_of_algebraMap,
        hintValDef a ha0, hintValDef (d:R) hd0] at this
    exact this

  have hspanx_ne : spanSingleton R⁰ x ≠ 0 := spanSingleton_ne_zero_iff.mpr hx
  have hspan_d_ne : (Ideal.span {(d:R)} : Ideal R) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr hd0
  have hspan_a_ne : (Ideal.span {a} : Ideal R) ≠ 0 := Ideal.span_singleton_eq_bot.not.mpr ha0
  have hcoe_d_ne : ((Ideal.span {(d:R)} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 :=
    coeIdeal_ne_zero.mpr hspan_d_ne
  have hspan : spanSingleton R⁰ x * (↑(Ideal.span {(d:R)}) : FractionalIdeal R⁰ K) =
      (↑(Ideal.span {a}) : FractionalIdeal R⁰ K) := by
    rw [coeIdeal_span_singleton, coeIdeal_span_singleton,
        spanSingleton_mul_spanSingleton, hxd]
  have hcount : count K v (spanSingleton R⁰ x) = (na : ℤ) - (nd : ℤ) := by
    have hc := congrArg (count K v) hspan
    rw [count_mul K v hspanx_ne hcoe_d_ne, count_coe K v hspan_a_ne,
        count_coe K v hspan_d_ne] at hc
    linarith

  have hexpd_ne : (WithZero.exp (-(nd:ℤ)) : WithZero (Multiplicative ℤ)) ≠ 0 :=
    WithZero.coe_ne_zero
  rw [eq_div_of_mul_eq hexpd_ne hval, hcount, ← WithZero.exp_sub]
  congr 1
  push_cast
  ring

end S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_valuation_eq_ofAdd_neg_count_spanSingleton (solution)
