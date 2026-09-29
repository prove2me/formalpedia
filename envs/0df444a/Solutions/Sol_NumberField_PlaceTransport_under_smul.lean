-- Prove2me | solution 1 for NumberField.PlaceTransport.under_smul
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.93214+00:00
-- url     : https://prove2.me/submissions/bb9efc0e-b4d0-5fd9-849b-a2007e03a4a6

import Mathlib
import Definitions.Def_NumberField_PlaceTransport
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_NumberField_PlaceTransport_under_smul

set_option autoImplicit false
open scoped NumberField.PlaceTransport

theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (σ : K ≃ₐ[E] K) (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    (σ • w).under (NumberField.RingOfIntegers E) = w.under (NumberField.RingOfIntegers E) := by
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [IsDedekindDomain.HeightOneSpectrum.under_asIdeal, IsDedekindDomain.HeightOneSpectrum.under_asIdeal]
  ext x
  rw [Ideal.mem_comap, Ideal.mem_comap, NumberField.PlaceTransport.mem_smul_asIdeal_iff]
  have : σ⁻¹ • (algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x)
      = algebraMap (NumberField.RingOfIntegers E) (NumberField.RingOfIntegers K) x :=
    Subtype.ext ((σ⁻¹).commutes _)
  rw [this]

end S_NumberField_PlaceTransport_under_smul
end P2MW
export P2MW.S_NumberField_PlaceTransport_under_smul (solution)
