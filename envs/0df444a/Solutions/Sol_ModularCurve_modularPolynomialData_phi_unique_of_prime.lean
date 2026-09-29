-- Prove2me | solution 1 for ModularCurve.modularPolynomialData_phi_unique_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8bceb970-059a-59ef-b201-60dc01cde0ab

import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_phiIrreducible_of_prime
import Theorems.Thm_ModularCurve_ModularPolynomialData_minpoly_jqN_eq
import Theorems.Thm_ModularCurve_evalAtJGen_injective
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_modularPolynomialData_phi_unique_of_prime
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve IntermediateField

theorem solution {ℓ : ℕ} [NeZero ℓ]
    (hℓ : ℓ.Prime) (data data' : ModularCurve.ModularPolynomialData ℓ) :
    data.Φ = data'.Φ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have h3 : data.Φ.map ModularCurve.evalAtJGen = data'.Φ.map ModularCurve.evalAtJGen :=
    (data.minpoly_jqN_eq (ModularCurve.phiIrreducible_of_prime ℓ data)).symm.trans
      (data'.minpoly_jqN_eq (ModularCurve.phiIrreducible_of_prime ℓ data'))
  exact Polynomial.map_injective ModularCurve.evalAtJGen ModularCurve.evalAtJGen_injective h3

end S_ModularCurve_modularPolynomialData_phi_unique_of_prime
end P2MW
export P2MW.S_ModularCurve_modularPolynomialData_phi_unique_of_prime (solution)
