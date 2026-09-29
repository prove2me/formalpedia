-- Prove2me | solution 1 for NumberField.PlaceDecomp.dvd_natCard_decomp_of_pow_eq_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bfa0e69b-c6bc-5957-ab69-5bf2ac5b530a

import Mathlib
import Definitions.Def_NumberField_PlaceDecompositionAction
import Theorems.Thm_NumberField_PlaceDecomp_natCard_decomp_eq_ramificationIdx_mul_inertiaDeg
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
open NumberField IsDedekindDomain
open scoped NumberField.PlaceDecomp

theorem solution
    (F : Type) [Field F] [NumberField F] [IsGalois ℚ F]
    (p : ℕ) [Fact p.Prime] (q : ℕ) [Fact q.Prime] (r : F) (hr : r ^ p = (q : F))
    (w : HeightOneSpectrum (𝓞 F)) (hw : ((q : ℕ) : 𝓞 F) ∈ w.asIdeal) :
    p ∣ Nat.card ↥(NumberField.PlaceDecomp.decomp ℚ F w) := by
  classical
  have hp : p.Prime := Fact.out
  have hq : q.Prime := Fact.out
  rw [NumberField.PlaceDecomp.natCard_decomp_eq_ramificationIdx_mul_inertiaDeg ℚ F w]
  apply Dvd.dvd.mul_right

  set P := (HeightOneSpectrum.under (𝓞 ℚ) w).asIdeal with hPdef
  have hPq : P = Ideal.span {((q : ℕ) : 𝓞 ℚ)} := by
    have hle : Ideal.span {((q : ℕ) : 𝓞 ℚ)} ≤ P := by
      rw [Ideal.span_singleton_le_iff_mem]
      show ((q : ℕ) : 𝓞 ℚ) ∈ Ideal.comap (algebraMap (𝓞 ℚ) (𝓞 F)) w.asIdeal
      rw [Ideal.mem_comap, map_natCast]
      exact hw

    have hmax : (Ideal.span {((q : ℕ) : 𝓞 ℚ)}).IsMaximal := by
      let f : 𝓞 ℚ →+* ℤ := (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).toRingHom
      have hf : Function.Surjective f := (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).surjective
      have hZ : (Ideal.span {(q : ℤ)}).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hq).irreducible
      have hcomap : Ideal.comap f (Ideal.span {(q : ℤ)}) = Ideal.span {((q : ℕ) : 𝓞 ℚ)} := by
        ext x
        rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
        constructor
        · intro h
          have h' := map_dvd (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).symm.toRingHom h
          rw [map_natCast] at h'
          have hx : (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).symm.toRingHom (f x) = x :=
            (Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ).symm_apply_apply x
          rwa [hx] at h'
        · intro h
          have h' := map_dvd f h
          rwa [map_natCast] at h'
      rw [← hcomap]
      exact Ideal.comap_isMaximal_of_surjective f hf
    exact (hmax.eq_of_le (HeightOneSpectrum.under (𝓞 ℚ) w).isPrime.ne_top hle).symm

  have hint : IsIntegral ℤ r := by
    refine ⟨Polynomial.X ^ p - Polynomial.C (q : ℤ), Polynomial.monic_X_pow_sub_C _ hp.ne_zero, ?_⟩
    simp [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, hr]
  let r' : 𝓞 F := ⟨r, (mem_integralClosure_iff ℤ F).mpr hint⟩
  have hr'coe : ((r' : 𝓞 F) : F) = r := rfl
  have hr' : (r' : 𝓞 F) ^ p = ((q : ℕ) : 𝓞 F) := by
    apply RingOfIntegers.coe_injective
    push_cast
    exact hr
  have hmap : Ideal.map (algebraMap (𝓞 ℚ) (𝓞 F)) P = (Ideal.span {r'}) ^ p := by
    rw [hPq, Ideal.map_span, Set.image_singleton, map_natCast, Ideal.span_singleton_pow, hr']
  have hr'0 : (r' : 𝓞 F) ≠ 0 := by
    intro h0
    have : ((q : ℕ) : 𝓞 F) = 0 := by rw [← hr', h0, zero_pow hp.ne_zero]
    exact (Nat.cast_ne_zero.mpr hq.ne_zero) (by exact_mod_cast congrArg ((↑) : 𝓞 F → F) this)
  have hne : Ideal.map (algebraMap (𝓞 ℚ) (𝓞 F)) P ≠ ⊥ := by
    rw [hmap]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hr'0)
  rw [Ideal.IsDedekindDomain.ramificationIdx'_eq_normalizedFactors_count hne w.isPrime w.ne_bot, hmap,
    UniqueFactorizationMonoid.normalizedFactors_pow, Multiset.count_nsmul]
  exact Dvd.intro _ rfl

end S_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime
end P2MW
export P2MW.S_NumberField_PlaceDecomp_dvd_natCard_decomp_of_pow_eq_prime (solution)
