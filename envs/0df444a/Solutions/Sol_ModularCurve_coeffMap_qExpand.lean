-- Prove2me | solution 1 for ModularCurve.coeffMap_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/388768f4-c83e-56ec-ae62-5a3757fac62e

import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_ModularCurve_X0
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_coeffMap_qExpand

open ModularCurve IntermediateField HahnSeries

theorem solution {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ) [NeZero n] (x : LaurentSeries R) : ModularCurve.coeffMap f (ModularCurve.qExpand R n x) = ModularCurve.qExpand S n (ModularCurve.coeffMap f x) :=
  by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]

end S_ModularCurve_coeffMap_qExpand
end P2MW
export P2MW.S_ModularCurve_coeffMap_qExpand (solution)
