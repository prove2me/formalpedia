-- Prove2me | solution 1 for ModularCurve.exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/9fdf0d7b-f6f8-5a2d-a719-c8b5e224efba

import Mathlib
import Definitions.Def_ModularCurve_X1
import Theorems.Thm_LaurentSeries_exists_eq_C_of_isAlgebraic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC

set_option autoImplicit false

open scoped MatrixGroups
open ModularCurve

theorem solution
    (Γ : Subgroup SL(2, ℤ)) (x : ↥(qExpFunctionFieldC ℚ Γ)) (hx : IsAlgebraic ℚ x) :
    ∃ c : ℚ, x = algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ) c := by

  have hx' : IsAlgebraic ℚ ((x : ↥(qExpFunctionFieldC ℚ Γ)) : LaurentSeries ℚ) := by
    obtain ⟨P, hP0, hPx⟩ := hx
    refine ⟨P, hP0, ?_⟩
    have key : (algebraMap ℚ (LaurentSeries ℚ)) =
        (algebraMap ↥(qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ)).comp (algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ)) :=
      RingHom.ext_rat _ _
    rw [Polynomial.aeval_def, key]
    change P.eval₂ ((algebraMap ↥(qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ)).comp (algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ)))
      (algebraMap ↥(qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ) x) = 0
    rw [← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hPx, map_zero]
  obtain ⟨c, hc⟩ := LaurentSeries.exists_eq_C_of_isAlgebraic _ hx'
  refine ⟨c, Subtype.ext ?_⟩
  rw [hc]
  exact RingHom.congr_fun (RingHom.ext_rat (HahnSeries.C : ℚ →+* LaurentSeries ℚ)
    ((algebraMap ↥(qExpFunctionFieldC ℚ Γ) (LaurentSeries ℚ)).comp (algebraMap ℚ ↥(qExpFunctionFieldC ℚ Γ)))) c

end S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC
end P2MW
export P2MW.S_ModularCurve_exists_eq_algebraMap_of_isAlgebraic_qExpFunctionFieldC (solution)
