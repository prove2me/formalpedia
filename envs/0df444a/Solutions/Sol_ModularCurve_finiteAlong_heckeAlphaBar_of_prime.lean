-- Prove2me | solution 1 for ModularCurve.finiteAlong_heckeAlphaBar_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/581f81af-d363-52f0-89b4-847ffdfe4ef8

import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_finiteAlong_heckeAlphaBar_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve AlgebraicCurve IntermediateField Polynomial

theorem solution (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [Fact ℓ.Prime] : AlgebraicCurve.FiniteAlong L (ModularCurve.heckeAlphaBar L N ℓ) := by
  obtain ⟨data, _⟩ := exists_modularPolynomialData_evalSymm ℓ
  exact finiteAlong_heckeAlphaBar_of_modularPolynomialData L data Fact.out N

end S_ModularCurve_finiteAlong_heckeAlphaBar_of_prime
end P2MW
export P2MW.S_ModularCurve_finiteAlong_heckeAlphaBar_of_prime (solution)
