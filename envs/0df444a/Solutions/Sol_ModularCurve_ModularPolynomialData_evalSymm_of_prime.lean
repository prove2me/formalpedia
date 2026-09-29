-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.evalSymm_of_prime
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/0b48ef04-6878-5a17-b179-5104d3e128ba

import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_ModularPolynomialData_eq_of_prime
import Theorems.Thm_ModularCurve_exists_modularPolynomialData_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_prime
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

theorem solution (p : ℕ) [hp : Fact (Nat.Prime p)] (data : ModularPolynomialData p) : EvalSymm data.Φ := by
  obtain ⟨d, hd⟩ := ModularCurve.exists_modularPolynomialData_evalSymm p
  rw [ModularCurve.ModularPolynomialData.eq_of_prime p data d]
  exact hd

end S_ModularCurve_ModularPolynomialData_evalSymm_of_prime
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_evalSymm_of_prime (solution)
