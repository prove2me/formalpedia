-- Prove2me | solution 1 for ModularCurve.isIntegral_adjoin_jq_modularUnitSeries_inv
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/8be42c8c-2ed8-5aa0-8c48-fe811d363c2b

import Definitions.Def_ModularCurve_ModularUnit
import Definitions.Def_ModularForm_HeckeOperator
import Mathlib.NumberTheory.ModularForms.Discriminant
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_hasSum_modularUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_hasSum_smul_modularUnitSeries_qParam
import Theorems.Thm_ModularCurve_discriminant_div_discriminant_heckeDiagMatrix_smul
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single"

set_option autoImplicit false

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] : IsIntegral (Algebra.adjoin ℚ {ModularCurve.jq}) (ModularCurve.modularUnitSeries ℓ)⁻¹ := by
  haveI : NeZero ℓ := ⟨(Fact.out : Nat.Prime ℓ).ne_zero⟩
  refine ModularCurve.isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ
    (ModularCurve.modularUnitSeries ℓ)⁻¹ (((ℓ : ℚ) ^ 12)⁻¹ • ModularCurve.modularUnitSeries ℓ)
    (fun τ => ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ)
      / ModularForm.discriminant τ)
    (fun τ => ModularCurve.hasSum_modularUnitSeries_inv_qParam ℓ τ)
    (fun τ => ModularCurve.hasSum_smul_modularUnitSeries_qParam ℓ τ)
    (fun γ hγ τ => ?_)
  show ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • γ • τ)
      / ModularForm.discriminant (γ • τ)
    = ModularForm.discriminant (ModularForm.heckeDiagMatrix ℓ • τ) / ModularForm.discriminant τ
  have h := congrArg Inv.inv
    (ModularCurve.discriminant_div_discriminant_heckeDiagMatrix_smul ℓ γ hγ τ)
  rwa [inv_div, inv_div] at h

end S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv
end P2MW
export P2MW.S_ModularCurve_isIntegral_adjoin_jq_modularUnitSeries_inv (solution)
