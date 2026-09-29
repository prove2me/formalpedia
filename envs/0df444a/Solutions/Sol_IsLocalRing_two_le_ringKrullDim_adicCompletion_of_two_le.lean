-- Prove2me | solution 1 for IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.353894+00:00
-- url     : https://prove2.me/submissions/a75c2509-2d16-5d9d-bdf7-f182cd2cc548

import Mathlib
import Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
set_option autoImplicit false

theorem solution
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by
  haveI : Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
    IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal R
  have h2 : (2 : ℕ) ≤ Order.krullDim (PrimeSpectrum R) := by
    show ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim R
    exact h
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp h2
  obtain ⟨Q, hQ⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat
    (A := R) (B := AdicCompletion (IsLocalRing.maximalIdeal R) R) l.last
  haveI : Q.asIdeal.LiesOver l.last.asIdeal := ⟨by rw [← hQ]; rfl⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l Q.asIdeal
  have := Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩
  exact this

end S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
end P2MW
export P2MW.S_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le (solution)
