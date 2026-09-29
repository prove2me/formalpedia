-- Prove2me | solution 1 for ModularCurve.FullLevel.exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:09.976215+00:00
-- url     : https://prove2.me/submissions/cda2512a-b409-5977-b853-c3f7c42c4478

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_FullLevel_exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
p2m_attr_erase "simp" "ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero"

set_option autoImplicit false

open ModularCurve

theorem solution
    (q : ℕ) [Fact q.Prime] (hq : 5 ≤ q) (M' : ℕ) [NeZero M'] (hqM' : ¬ q ∣ M')
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓq : ℓ ≠ q) (hℓM' : ¬ ℓ ∣ M')
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {q * ℓ} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ q)
    (ξ : L) (hξ : IsPrimitiveRoot ξ (q * ℓ))
    (K : IntermediateField L (LaurentSeries L))
    (hK : K = ModularCurve.laurentBaseChange L
      (ModularCurve.xHFunctionField ((q * ℓ) ^ 2 * M')
        (ModularCurve.FullLevel.levelH (q * ℓ) M'))) :
    haveI : NeZero (q * ℓ) := ⟨Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero⟩
    ∃ C : WeierstrassCurve.VariableChange (LaurentSeries L),
      (C • ModularCurve.tateBase L (q * ℓ)).a₁ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₂ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₃ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₄ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      (C • ModularCurve.tateBase L (q * ℓ)).a₆ ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
      ∀ v w : Fin 2 → ZMod (q * ℓ), v ≠ 0 → w ≠ 0 →
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).xP ∈ Set.range ((↑) : ↥K → LaurentSeries L) ∧
        ((ModularCurve.cuspData L (q * ℓ) (hξ.isUnit (Nat.mul_ne_zero (Fact.out : q.Prime).ne_zero (Fact.out : ℓ.Prime).ne_zero)).unit v w).variableChange C).yP ∈ Set.range ((↑) : ↥K → LaurentSeries L) := by
  obtain ⟨C, -, -, -, -, h⟩ :=
    ModularCurve.FullLevel.exists_variableChange_weightOne_tateBase_mem_laurentBaseChange_and_cuspData_mem
      q hq M' hqM' ℓ hℓ3 hℓq hℓM' L ζ hζ ξ hξ K hK
  exact ⟨C, h⟩

end S_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem
end P2MW
export P2MW.S_ModularCurve_FullLevel_exists_variableChange_tateBase_mem_laurentBaseChange_and_cuspData_mem (solution)
