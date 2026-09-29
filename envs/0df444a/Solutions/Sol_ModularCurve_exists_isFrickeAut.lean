-- Prove2me | solution 1 for ModularCurve.exists_isFrickeAut
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/05df5b93-8ddd-5a54-a893-1f6a67048873

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_exists_isFrickeAut_of_modularPolynomialData
import Theorems.Thm_ModularCurve_exists_phiIrreducible_evalSymm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_isFrickeAut
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve AlgebraicCurve IntermediateField

noncomputable section

theorem solution (ℓ : ℕ) [hℓ : Fact (Nat.Prime ℓ)] : ∃ σ : modularFunctionField ℓ ≃ₐ[ℚ] modularFunctionField ℓ, IsFrickeAut ℓ σ := by
  obtain ⟨data, hirr, hsymm⟩ := ModularCurve.exists_phiIrreducible_evalSymm ℓ
  exact ModularCurve.exists_isFrickeAut_of_modularPolynomialData data hsymm hirr

end

end S_ModularCurve_exists_isFrickeAut
end P2MW
export P2MW.S_ModularCurve_exists_isFrickeAut (solution)
