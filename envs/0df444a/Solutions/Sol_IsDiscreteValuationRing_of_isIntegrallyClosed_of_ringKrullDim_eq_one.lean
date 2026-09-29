-- Prove2me | solution 1 for IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:07.85352+00:00
-- url     : https://prove2.me/submissions/9b62944a-56c3-5c1f-8303-930941ef5808

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one

namespace IsDiscreteValuationRing p2m_export "IsDiscreteValuationRing" "mk TFAE" end IsDiscreteValuationRing
p2m_open_scoped "IsDiscreteValuationRing" in

theorem IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R := by
  have hnf : ¬ IsField R := fun hf => by
    have h0 := ringKrullDim_eq_zero_of_isField hf
    rw [h] at h0
    exact one_ne_zero h0
  have hdim : Ring.DimensionLEOne R := by
    refine ⟨fun {p} hp hpp => ?_⟩
    obtain ⟨m, hm, hpm⟩ := Ideal.exists_le_maximal p hpp.ne_top
    by_contra hnot
    have hlt : p < m := lt_of_le_of_ne hpm (fun e => hnot (e ▸ hm))
    have hmh : (m.height : WithBot ℕ∞) ≤ 1 := by
      rw [← h]
      exact (ringKrullDim_le_iff_isMaximal_height_le (ringKrullDim R)).mp le_rfl hm
    have hmh' : m.height ≤ (1 : ℕ) := by exact_mod_cast hmh
    rw [Ideal.height_le_iff] at hmh'
    have hp0 : p.height = 0 := by
      exact ENat.lt_one_iff_eq_zero.mp (hmh' p hpp hlt)
    rw [Ideal.height_eq_zero_iff] at hp0
    exact hp (le_bot_iff.mp (hp0.2 ⟨Ideal.isPrime_bot, le_rfl⟩ bot_le))
  have hded : IsDedekindRing R := IsDedekindRing.mk
  have hdd : IsDedekindDomain R := IsDedekindDomain.mk
  exact ((IsDiscreteValuationRing.TFAE R hnf).out 0 2).mpr hdd

theorem solution
    (R : Type*) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R] [IsIntegrallyClosed R]
    (h : ringKrullDim R = 1) : IsDiscreteValuationRing R :=
  IsDiscreteValuationRing.of_isIntegrallyClosed_of_ringKrullDim_eq_one R h

end S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one
end P2MW
export P2MW.S_IsDiscreteValuationRing_of_isIntegrallyClosed_of_ringKrullDim_eq_one (solution)
