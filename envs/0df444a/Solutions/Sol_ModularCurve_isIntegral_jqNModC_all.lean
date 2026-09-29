-- Prove2me | solution 1 for ModularCurve.isIntegral_jqNModC_all
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/2514932a-9210-58ac-b027-81358136b2f5

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_ModularCurve_PhiGen
import Theorems.Thm_ModularCurve_isIntegral_jqNModC_all_of_modularPolynomialFamily
import Theorems.Thm_ModularCurve_modularPolynomialFamily
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_jqNModC_all
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open ModularCurve

theorem solution (K : Type*) [Field K] (N : ℕ) [NeZero N] :
    IsIntegral (IntermediateField.adjoin K ({jqModC K} : Set (LaurentSeries K))) (jqNModC K N) :=
  isIntegral_jqNModC_all_of_modularPolynomialFamily K modularPolynomialFamily N

#print axioms solution

end S_ModularCurve_isIntegral_jqNModC_all
end P2MW
export P2MW.S_ModularCurve_isIntegral_jqNModC_all (solution)
