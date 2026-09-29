-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/f391e8ad-0d9c-5bd4-bb31-aa7ac481f4c3

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem solution
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ)) :
    ∃ p : ℕ, p.Prime ∧ v.asIdeal = Ideal.span {(p : 𝓞 ℚ)} := by
  refine ⟨Rat.HeightOneSpectrum.natGenerator v, Rat.HeightOneSpectrum.prime_natGenerator v, ?_⟩
  set e : 𝓞 ℚ ≃+* ℤ := Rat.IsIntegralClosure.intEquiv (𝓞 ℚ) with he
  have h : Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal = Ideal.span {((Rat.HeightOneSpectrum.natGenerator v : ℕ) : ℤ)} :=
    (Rat.HeightOneSpectrum.span_natGenerator (R := 𝓞 ℚ) v).symm
  have h3 : Ideal.map (e.symm : ℤ →+* 𝓞 ℚ) (Ideal.map (e : 𝓞 ℚ →+* ℤ) v.asIdeal) = v.asIdeal :=
    Ideal.map_of_equiv e
  rw [← h3, h, Ideal.map_span, Set.image_singleton]
  congr 2
  simp

end S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_prime_and_asIdeal_eq_span_ringOfIntegers_rat (solution)
