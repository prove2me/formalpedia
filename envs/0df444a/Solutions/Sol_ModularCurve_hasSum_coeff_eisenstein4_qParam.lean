-- Prove2me | solution 1 for ModularCurve.hasSum_coeff_eisenstein4_qParam
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/18e31428-5030-5f3d-a8d1-0c7d08ebae20

import Mathlib
import Definitions.Def_ModularCurve_X0
import Theorems.Thm_ModularCurve_qExpansion_E4_eq_map_eisenstein4
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_hasSum_coeff_eisenstein4_qParam
set_option autoImplicit false

open ModularCurve
open scoped MatrixGroups

theorem solution (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => ((PowerSeries.coeff m eisenstein4 : ℤ) : ℂ) * Function.Periodic.qParam 1 (τ : ℂ) ^ m)
      (ModularForm.E₄ τ) := by
  have h := UpperHalfPlane.hasSum_qExpansion (f := ⇑ModularForm.E₄) one_pos
    (SlashInvariantFormClass.periodic_comp_ofComplex ModularForm.E₄ one_mem_strictPeriods_SL)
    (ModularFormClass.holo ModularForm.E₄) (ModularFormClass.bdd_at_infty ModularForm.E₄) τ
  rw [ModularCurve.qExpansion_E4_eq_map_eisenstein4] at h
  simpa only [PowerSeries.coeff_map, smul_eq_mul, eq_intCast] using h

end S_ModularCurve_hasSum_coeff_eisenstein4_qParam
end P2MW
export P2MW.S_ModularCurve_hasSum_coeff_eisenstein4_qParam (solution)
