-- Prove2me | solution 1 for LaurentSeries.heckeV_eq_qExpand
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/12b7eefd-6c4d-5290-92db-e0557151b5ea

import Mathlib
import Definitions.Def_LaurentSeries_HeckeU
import Definitions.Def_LaurentSeries_HeckeV
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_LaurentCoeff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LaurentSeries_heckeV_eq_qExpand

set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

set_option autoImplicit false

open ModularCurve LaurentSeries

theorem solution (R : Type*) [CommRing R] (ℓ : ℕ) [NeZero ℓ] (f : LaurentSeries R) :
    heckeV R ℓ (Nat.pos_of_ne_zero (NeZero.ne ℓ)) f = qExpand R ℓ f  := by
  ext n
  rw [coeff_heckeV]
  split_ifs with h
  · obtain ⟨m, rfl⟩ := h
    have hℓ0 : (ℓ : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne ℓ
    rw [Int.mul_ediv_cancel_left _ hℓ0, qExpand_coeff_mul]
  · rw [qExpand_coeff_of_not_dvd _ _ h]

end S_LaurentSeries_heckeV_eq_qExpand
end P2MW
export P2MW.S_LaurentSeries_heckeV_eq_qExpand (solution)
