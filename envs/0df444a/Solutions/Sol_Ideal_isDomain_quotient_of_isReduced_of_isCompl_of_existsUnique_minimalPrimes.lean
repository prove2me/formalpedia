-- Prove2me | solution 1 for Ideal.isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/da21aff7-ec1d-5309-a8e3-62d8bcef6c1b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes

set_option autoImplicit false

theorem solution
    (R : Type) [CommRing R] [IsReduced R] (I J : Ideal R) (hIJ : IsCompl I J)
    [Nontrivial (R ⧸ I)]
    (huniq : ∃! 𝔭 : Ideal R, 𝔭 ∈ (⊥ : Ideal R).minimalPrimes ∧ I ≤ 𝔭) :
    IsDomain (R ⧸ I) := by
  have hinf : I ⊓ J = ⊥ := hIJ.inf_eq_bot
  have hsup : I ⊔ J = ⊤ := hIJ.sup_eq_top
  have hIJ0 : I * J = ⊥ := le_bot_iff.mp (Ideal.mul_le_inf.trans hinf.le)

  have hrad : I.IsRadical := by
    intro x hx
    obtain ⟨n, hn⟩ := (Ideal.mem_radical_iff).mp hx
    obtain ⟨i, hi, j, hj, hij⟩ := Ideal.isCoprime_iff_exists.mp (Ideal.isCoprime_iff_sup_eq.mpr hsup)
    rcases Nat.eq_zero_or_pos n with h0 | hnpos
    · subst h0
      rw [pow_zero] at hn
      have : I = ⊤ := I.eq_top_of_isUnit_mem hn isUnit_one
      rw [this]; trivial
    have hxj : IsNilpotent (x * j) := by
      refine ⟨n, ?_⟩
      have hmem : (x * j) ^ n ∈ I * J := by
        rw [mul_pow]
        exact Ideal.mul_mem_mul hn (J.pow_mem_of_mem hj n hnpos)
      rw [hIJ0] at hmem
      exact (Ideal.mem_bot).mp hmem
    have hxj0 : x * j = 0 := hxj.eq_zero
    have : x = x * i := by
      calc x = x * (i + j) := by rw [hij, mul_one]
        _ = x * i := by rw [mul_add, hxj0, add_zero]
    rw [this]
    exact I.mul_mem_left x hi

  obtain ⟨𝔭, ⟨h𝔭min, hI𝔭⟩, h𝔭uniq⟩ := huniq
  haveI h𝔭p : 𝔭.IsPrime := h𝔭min.1.1

  have hmin : ∀ 𝔮 ∈ I.minimalPrimes, 𝔮 = 𝔭 := by
    intro 𝔮 h𝔮
    apply h𝔭uniq
    refine ⟨⟨⟨h𝔮.1.1, bot_le⟩, ?_⟩, h𝔮.1.2⟩
    rintro r ⟨hr, -⟩ hr𝔮
    have hIr : I ≤ r := by
      have hIJr : I * J ≤ r := by rw [hIJ0]; exact bot_le
      rcases hr.mul_le.mp hIJr with h | h
      · exact h
      · exfalso
        apply h𝔮.1.1.ne_top
        rw [eq_top_iff, ← hsup]
        exact sup_le h𝔮.1.2 (h.trans hr𝔮)
    exact h𝔮.2 ⟨hr, hIr⟩ hr𝔮

  obtain ⟨𝔮₀, h𝔮₀, -⟩ := Ideal.exists_minimalPrimes_le hI𝔭
  have h𝔭I : 𝔭 ∈ I.minimalPrimes := hmin 𝔮₀ h𝔮₀ ▸ h𝔮₀
  have hIeq : I = 𝔭 := by
    apply le_antisymm hI𝔭
    calc 𝔭 ≤ sInf I.minimalPrimes := le_sInf fun 𝔮 h𝔮 => (hmin 𝔮 h𝔮).symm.le
      _ = I.radical := Ideal.sInf_minimalPrimes
      _ = I := (Ideal.radical_eq_iff).mpr hrad
  rw [Ideal.Quotient.isDomain_iff_prime, hIeq]
  exact h𝔭p

end S_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes
end P2MW
export P2MW.S_Ideal_isDomain_quotient_of_isReduced_of_isCompl_of_existsUnique_minimalPrimes (solution)
