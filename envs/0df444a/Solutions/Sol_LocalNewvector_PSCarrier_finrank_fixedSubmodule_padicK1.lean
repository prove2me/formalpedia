-- Prove2me | solution 1 for LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:08.670037+00:00
-- url     : https://prove2.me/submissions/eac2daa4-8f35-56cd-ab48-855ae781fc82

import Definitions.Def_LocalNewvector_CharConductor
import Definitions.Def_LocalNewvector_PrincipalSeriesCarrier
import Theorems.Thm_LocalNewvector_PSCarrier_hasNewvectorConductor_add
import Theorems.Thm_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1_of_add_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
p2m_attr_erase "instance" "FLT.SmoothVectors.RightTranslationFn.instAddCommMonoid FLT.SmoothVectors.RightTranslationFn.instMulAction FLT.SmoothVectors.RightTranslationFn.instDistribMulAction instContinuousSMulOfDiscreteTopologyOfContinuousSMulDiscrete FLT.SpectralSide.instCompactSpaceMatrix"
p2m_attr_erase "simp" "FLT.SmoothVectors.RightTranslationFn.toFun_smul FLT.SmoothVectors.RightTranslationFn.mk_toFun FLT.SmoothVectors.RightTranslationFn.toFun_mk FLT.SmoothVectors.mem_smoothVectors_iff LocalGL2.coe_localRepSome LocalGL2.coe_diagPi LocalGL2.coe_localRepInf LocalGL2.coe_localRepSome_inv LocalGL2.coe_unipotentInt LocalGL2.coe_weylInt LocalGL2.coe_diagPi_inv"

set_option autoImplicit false

namespace FLT
namespace PrincipalSeriesGL2Padic
p2m_open "FLT"

theorem PSCarrier.finrank_fixedSubmodule_padicK1_impl (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂)
    (m : ℕ) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (LocalNewvector.PSCarrier p μ₁ μ₂))
        = m + 1 - (n₁ + n₂) := by
  rcases Nat.lt_or_ge m (n₁ + n₂) with hm | hm
  · rw [(LocalNewvector.PSCarrier.hasNewvectorConductor_add p h₁ h₂).2 m hm, finrank_bot]; omega
  · rw [LocalNewvector.PSCarrier.finrank_fixedSubmodule_padicK1_of_add_le p h₁ h₂ hm]; omega

end FLT.PrincipalSeriesGL2Padic

#print axioms FLT.PrincipalSeriesGL2Padic.PSCarrier.finrank_fixedSubmodule_padicK1_impl

theorem solution (p : ℕ) [Fact p.Prime] {μ₁ μ₂ : ℚ_[p]ˣ →* ℂˣ}
    {n₁ n₂ : ℕ} (h₁ : LocalNewvector.HasCharConductor p μ₁ n₁) (h₂ : LocalNewvector.HasCharConductor p μ₂ n₂)
    (m : ℕ) :
    Module.finrank ℂ
      ↥(LocalNewvector.fixedSubmodule (LocalNewvector.padicK1 p m) (LocalNewvector.PSCarrier p μ₁ μ₂))
        = m + 1 - (n₁ + n₂) := by
  exact FLT.PrincipalSeriesGL2Padic.PSCarrier.finrank_fixedSubmodule_padicK1_impl p h₁ h₂ m

end S_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1
end P2MW
export P2MW.S_LocalNewvector_PSCarrier_finrank_fixedSubmodule_padicK1 (solution)
