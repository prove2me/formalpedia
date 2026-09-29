-- Prove2me | solution 1 for ModularCurve.heckeBetaBarIntegral_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0bb0b1ba-406a-5b21-92cd-7310998be77f

import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_heckeBetaBarIntegral_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeBetaBarIntegral_of_prime
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve AlgebraicCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] : ModularCurve.HeckeBetaBarIntegral L N ℓ := by
  obtain ⟨data, hsymm⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact heckeBetaBarIntegral_of_modularPolynomialData L data hsymm Fact.out N

end S_ModularCurve_heckeBetaBarIntegral_of_prime
end P2MW
export P2MW.S_ModularCurve_heckeBetaBarIntegral_of_prime (solution)
