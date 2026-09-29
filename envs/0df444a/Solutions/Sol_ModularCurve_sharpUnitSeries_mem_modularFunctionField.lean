-- Prove2me | solution 1 for ModularCurve.sharpUnitSeries_mem_modularFunctionField
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/5b1f6877-230b-57bf-95f7-924a909bd12b

import Definitions.Def_ModularCurve_EtaQuotient
import Definitions.Def_ModularCurve_AtkinLehner
import Theorems.Thm_ModularCurve_mem_modularFunctionField_of_hasSum_of_gamma0_invariant
import Theorems.Thm_ModularCurve_isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant
import Theorems.Thm_ModularCurve_coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant
import Theorems.Thm_ModularCurve_hasSum_sharpUnitSeries_qParam
import Theorems.Thm_ModularCurve_hasSum_smul_sharpUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_hasSum_sharpUnitSeries_inv_qParam
import Theorems.Thm_ModularCurve_hasSum_smul_sharpUnitSeries_qParam
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_sharpUnitSeries_mem_modularFunctionField
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ"

set_option autoImplicit false

namespace ModularCurve
p2m_export "ModularCurve" "sharpExp sharpUnitFun sharpUnitSeries SharpUnitInvariant jq modularFunctionField modularFunctionFieldFull frickeInvolutionFull mem_modularFunctionField_of_hasSum_of_gamma0_invariant isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant hasSum_sharpUnitSeries_qParam hasSum_smul_sharpUnitSeries_inv_qParam hasSum_sharpUnitSeries_inv_qParam hasSum_smul_sharpUnitSeries_qParam"
p2m_open "ModularCurve"

namespace EIT

variable (ℓ : ℕ) [Fact (Nat.Prime ℓ)]

omit [Fact (Nat.Prime ℓ)] in

theorem inv_invariant (hW : SharpUnitInvariant ℓ) :
    ∀ γ ∈ CongruenceSubgroup.Gamma0 ℓ, ∀ τ : UpperHalfPlane,
      (sharpUnitFun ℓ (γ • τ))⁻¹ = (sharpUnitFun ℓ τ)⁻¹ :=
  fun γ hγ τ => by rw [hW γ hγ τ]

theorem sharpUnitSeries_mem_modularFunctionField (hW : SharpUnitInvariant ℓ) :
    sharpUnitSeries ℓ ∈ modularFunctionField ℓ :=
  mem_modularFunctionField_of_hasSum_of_gamma0_invariant ℓ (sharpUnitSeries ℓ)
    ((ℓ : ℚ) ^ (sharpExp ℓ / 2) • (sharpUnitSeries ℓ)⁻¹) (sharpUnitFun ℓ)
    (hasSum_sharpUnitSeries_qParam ℓ) (hasSum_smul_sharpUnitSeries_inv_qParam ℓ) hW

theorem isIntegral_adjoin_jq_sharpUnitSeries (hW : SharpUnitInvariant ℓ) :
    IsIntegral (Algebra.adjoin ℚ {jq}) (sharpUnitSeries ℓ) :=
  isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ (sharpUnitSeries ℓ)
    ((ℓ : ℚ) ^ (sharpExp ℓ / 2) • (sharpUnitSeries ℓ)⁻¹) (sharpUnitFun ℓ)
    (hasSum_sharpUnitSeries_qParam ℓ) (hasSum_smul_sharpUnitSeries_inv_qParam ℓ) hW

theorem isIntegral_adjoin_jq_sharpUnitSeries_inv (hW : SharpUnitInvariant ℓ) :
    IsIntegral (Algebra.adjoin ℚ {jq}) (sharpUnitSeries ℓ)⁻¹ :=
  isIntegral_adjoin_jq_of_hasSum_of_gamma0_invariant ℓ (sharpUnitSeries ℓ)⁻¹
    (((ℓ : ℚ) ^ (sharpExp ℓ / 2))⁻¹ • sharpUnitSeries ℓ) (fun τ => (sharpUnitFun ℓ τ)⁻¹)
    (hasSum_sharpUnitSeries_inv_qParam ℓ) (hasSum_smul_sharpUnitSeries_qParam ℓ) (inv_invariant ℓ hW)

theorem coe_frickeInvolutionFull_sharpUnitSeries (hW : SharpUnitInvariant ℓ)
    (hmem : sharpUnitSeries ℓ ∈ modularFunctionFieldFull ℓ) :
    ((frickeInvolutionFull ℓ ⟨sharpUnitSeries ℓ, hmem⟩ : modularFunctionFieldFull ℓ) : LaurentSeries ℚ) =
      (ℓ : ℚ) ^ (sharpExp ℓ / 2) • (sharpUnitSeries ℓ)⁻¹ :=
  coe_frickeInvolutionFull_eq_of_hasSum_of_gamma0_invariant ℓ (sharpUnitSeries ℓ)
    ((ℓ : ℚ) ^ (sharpExp ℓ / 2) • (sharpUnitSeries ℓ)⁻¹) (sharpUnitFun ℓ)
    (hasSum_sharpUnitSeries_qParam ℓ) (hasSum_smul_sharpUnitSeries_inv_qParam ℓ) hW hmem

end EIT

end ModularCurve

theorem solution (ℓ : ℕ) [Fact (Nat.Prime ℓ)] (hW : ModularCurve.SharpUnitInvariant ℓ) : ModularCurve.sharpUnitSeries ℓ ∈ ModularCurve.modularFunctionField ℓ :=
  ModularCurve.EIT.sharpUnitSeries_mem_modularFunctionField ℓ hW

end S_ModularCurve_sharpUnitSeries_mem_modularFunctionField
end P2MW
export P2MW.S_ModularCurve_sharpUnitSeries_mem_modularFunctionField (solution)
