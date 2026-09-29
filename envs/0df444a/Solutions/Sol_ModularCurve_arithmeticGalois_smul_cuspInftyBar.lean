-- Prove2me | solution 1 for ModularCurve.arithmeticGalois_smul_cuspInftyBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/5513dacb-86a0-52df-9cf0-41b9e9c7d73e

import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticGalois_smul_cuspInftyBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    arithmeticGalois (modularFunctionFieldFull N) τ • cuspInftyBar N = cuspInftyBar N := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring, cuspInftyBar_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]
  exact ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff N τ⁻¹ x

end S_ModularCurve_arithmeticGalois_smul_cuspInftyBar
end P2MW
export P2MW.S_ModularCurve_arithmeticGalois_smul_cuspInftyBar (solution)
