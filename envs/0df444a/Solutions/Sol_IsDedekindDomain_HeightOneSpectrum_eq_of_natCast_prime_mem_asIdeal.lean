-- Prove2me | solution 1 for IsDedekindDomain.HeightOneSpectrum.eq_of_natCast_prime_mem_asIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/54cae070-9440-53c2-96cf-19a9a8f0d084

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem natCast_mem_asIdeal_iff' (w : HeightOneSpectrum (𝓞 ℚ)) (n : ℕ) :
    (n : 𝓞 ℚ) ∈ w.asIdeal ↔ Rat.HeightOneSpectrum.natGenerator w ∣ n := by
  rw [Rat.HeightOneSpectrum.natGenerator_dvd_iff,
    ← map_natCast (Rat.IsIntegralClosure.intEquiv (𝓞 ℚ)) n, Ideal.apply_mem_of_equiv_iff]

theorem natGenerator_eq_of_prime_mem' {p : ℕ} (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ))
    (hv : (p : 𝓞 ℚ) ∈ v.asIdeal) : Rat.HeightOneSpectrum.natGenerator v = p :=
  (Nat.prime_dvd_prime_iff_eq (Rat.HeightOneSpectrum.prime_natGenerator v) hp).1
    ((natCast_mem_asIdeal_iff' v p).1 hv)

theorem solution
    {r : ℕ} (hr : r.Prime) {v w : HeightOneSpectrum (𝓞 ℚ)}
    (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal) (hw : ((r : ℕ) : 𝓞 ℚ) ∈ w.asIdeal) : w = v := by
  have e1 := natGenerator_eq_of_prime_mem' hr w hw
  have e2 := natGenerator_eq_of_prime_mem' hr v hv
  have : Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) w = Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ) v :=
    Subtype.ext (e1.trans e2.symm)
  exact (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).injective this

end S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal
end P2MW
export P2MW.S_IsDedekindDomain_HeightOneSpectrum_eq_of_natCast_prime_mem_asIdeal (solution)
