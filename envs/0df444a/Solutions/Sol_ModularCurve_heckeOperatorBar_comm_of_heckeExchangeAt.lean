-- Prove2me | solution 1 for ModularCurve.heckeOperatorBar_comm_of_heckeExchangeAt
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0f7977e2-9409-5353-af04-94f1f5e2f206

import Definitions.Def_ModularCurve_DegeneracyTower
import Definitions.Def_ModularCurve_HeckeModule
import Theorems.Thm_ModularCurve_heckeDivBar_comm_of_heckeExchangeAt
import Theorems.Thm_ModularCurve_towerInclBar_isIntegral
import Theorems.Thm_ModularCurve_towerSubstBar_isIntegral
import Theorems.Thm_AlgebraicCurve_Pic0_correspondence_correspondence_comm
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.jqNModC_one ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

open ModularCurve AlgebraicCurve

theorem solution (N ℓ ℓ' M : ℕ) [NeZero N] [Fact ℓ.Prime] [Fact ℓ'.Prime] [NeZero M] (hM : M = N * ℓ * ℓ') (hM' : M = N * ℓ' * ℓ) [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ))] [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar (N * ℓ'))] [HasPrincipalDivisors (AlgebraicClosure ℚ) (modularFunctionFieldBar M)] (hex : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ ℓ' M hM) (hex' : HeckeExchangeAt (AlgebraicClosure ℚ) N ℓ' ℓ M hM') : heckeOperatorBar N ⟨ℓ, Fact.out⟩ * heckeOperatorBar N ⟨ℓ', Fact.out⟩ = heckeOperatorBar N ⟨ℓ', Fact.out⟩ * heckeOperatorBar N ⟨ℓ, Fact.out⟩ := by
  set L := AlgebraicClosure ℚ
  by_cases h₁ : HeckeInputsAlong L N ℓ
  swap
  · have z : heckeOperatorBar N ⟨ℓ, Fact.out⟩ = 0 := by
      apply LinearMap.ext; intro x
      rw [heckeOperatorBar_apply]
      show heckeOperatorAlong L N ℓ x = 0
      rw [heckeOperatorAlong_of_not h₁]; rfl
    rw [z, mul_zero, zero_mul]
  by_cases h₂ : HeckeInputsAlong L N ℓ'
  swap
  · have z : heckeOperatorBar N ⟨ℓ', Fact.out⟩ = 0 := by
      apply LinearMap.ext; intro x
      rw [heckeOperatorBar_apply]
      show heckeOperatorAlong L N ℓ' x = 0
      rw [heckeOperatorAlong_of_not h₂]; rfl
    rw [z, mul_zero, zero_mul]
  obtain ⟨hα, hβ, _, hfin, hFI, hN⟩ := h₁
  obtain ⟨hα', hβ', _, hfin', hFI', hN'⟩ := h₂
  apply LinearMap.ext; intro x
  show heckeOperatorAlong L N ℓ (heckeOperatorAlong L N ℓ' x) = heckeOperatorAlong L N ℓ' (heckeOperatorAlong L N ℓ x)
  rw [heckeOperatorAlong_eq hα hβ hFI hfin hN, heckeOperatorAlong_eq hα' hβ' hFI' hfin' hN']
  refine AlgebraicCurve.Pic0.correspondence_correspondence_comm _ _ _ _ hβ hα hβ' hα' hFI hfin hN hFI' hfin' hN'
    (fun D => ?_) x
  exact ModularCurve.heckeDivBar_comm_of_heckeExchangeAt L hM hM' hα hβ hα' hβ'
    (ModularCurve.towerInclBar_isIntegral L _) (ModularCurve.towerSubstBar_isIntegral L ℓ _)
    (ModularCurve.towerInclBar_isIntegral L _) (ModularCurve.towerSubstBar_isIntegral L ℓ' _) hex hex' D

end S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt
end P2MW
export P2MW.S_ModularCurve_heckeOperatorBar_comm_of_heckeExchangeAt (solution)
