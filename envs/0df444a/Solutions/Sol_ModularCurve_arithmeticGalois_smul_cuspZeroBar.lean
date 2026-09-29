-- Prove2me | solution 1 for ModularCurve.arithmeticGalois_smul_cuspZeroBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:11.261198+00:00
-- url     : https://prove2.me/submissions/3665616d-4cf9-503f-89cc-75c7e5320b18

import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_mem_qIntegersBar_iff
import Theorems.Thm_ModularCurve_arithmeticGalois_smul_geomAut
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_arithmeticGalois_smul_cuspZeroBar

open ModularCurve AlgebraicCurve
open scoped Pointwise

theorem solution (N : ℕ) [NeZero N] (τ : (AlgebraicClosure ℚ) ≃ₐ[ℚ] (AlgebraicClosure ℚ)) :
    arithmeticGalois (modularFunctionFieldFull N) τ • cuspZeroBar N = cuspZeroBar N := by
  apply Place.ext
  rw [SemilinearAut.smul_toValuationSubring, cuspZeroBar_def, Place.smul_toValuationSubring,
    cuspInftyBar_toValuationSubring]
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv, frickeInvolutionBar_def, ← map_inv]
  change geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)⁻¹
      (arithmeticGalois (modularFunctionFieldFull N) τ⁻¹ • x) ∈ _ ↔
    geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) (frickeInvolutionFull N)⁻¹ x ∈ _
  rw [← ModularCurve.arithmeticGalois_smul_geomAut (AlgebraicClosure ℚ) (modularFunctionFieldFull N) τ⁻¹ (frickeInvolutionFull N)⁻¹ x]
  exact ModularCurve.arithmeticGalois_smul_mem_qIntegersBar_iff N τ⁻¹ _

end S_ModularCurve_arithmeticGalois_smul_cuspZeroBar
end P2MW
export P2MW.S_ModularCurve_arithmeticGalois_smul_cuspZeroBar (solution)
