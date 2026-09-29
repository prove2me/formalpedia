-- Prove2me | solution 1 for ModularCurve.isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/1048b1a3-def5-5a7e-8843-651563901d62

import Definitions.Def_ModularCurve_JqCoeff
import Definitions.Def_AlgebraicCurve_TwoChartIntegralModel
import Definitions.Def_ModularCurve_X1
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_ModularCurve_FullLevelJacobian
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_ModularCurve_FullLevelLevelAutAt
import Definitions.Def_ModularCurve_LevelModuliPackage
import Definitions.Def_ModularCurve_LevelModuliPackageAbs
import Definitions.Def_ModularCurve_WeierstrassLevelModuliDatum
import Definitions.Def_ModularCurve_WeierstrassLevelComponents
import Definitions.Def_ModularCurve_WeierstrassGamma0Pow
import Definitions.Def_WeierstrassCurve_DrinfeldBasisGlobal
import Definitions.Def_WeierstrassCurve_DrinfeldTransportPin
import Definitions.Def_WeierstrassCurve_SectionAtOrigin
import Definitions.Def_WeierstrassCurve_DrinfeldLevelFunctor
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_WeierstrassCurve_PointChart
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Definitions.Def_ModularCurve_WeierstrassGamma1Pow
import Definitions.Def_ModularCurve_WeierstrassH1Pow

import Theorems.Thm_ModularCurve_isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst
import Theorems.Thm_ModularCurve_toricPoint_add_toricPoint_tateBase_of_charZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "WeierstrassCurve.kernelPolynomial_singleton WeierstrassCurve.kernelPolynomial_empty WeierstrassCurve.Affine.Point.coordsOrZero_some WeierstrassCurve.Affine.Point.coordsOrZero_zero compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero TateCurve.tateTorsionPoint_zero_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero"
p2m_attr_erase "simp" "WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero"

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry ModularCurve WeierstrassCurve.DrinfeldGlobal WeierstrassProjModel
open scoped MatrixGroups

theorem solution
    (F : Type) [Field F] [CharZero F] (q : ℕ) [NeZero q]
    (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2)
    (c : Fˣ) (hc : IsPrimitiveRoot (c : F) ℓ) :
    ModularCurve.IsGamma1Point (ModularCurve.tateBase F q) ℓ
      (⟨(ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2,
        (ModularCurve.tateToricPoint F q c).1, (ModularCurve.tateToricPoint F q c).2⟩ : ModularCurve.LevelPData (LaurentSeries F)) := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hℓ3 : 3 ≤ ℓ := by
    rcases hℓ.eq_two_or_odd' with h | h
    · exact absurd h hℓ2
    · have := hℓ.two_le; omega
  have hc0 : (c : F) ≠ 0 := Units.ne_zero c
  have hc1 : (c : F) ≠ 1 := hc.ne_one (by omega)

  obtain ⟨hns, -, -⟩ := ModularCurve.toricPoint_add_toricPoint_tateBase_of_charZero F q (c : F) (c : F) hc0 hc0 hc1 hc1
  have heq : (ModularCurve.tateBase F q).toAffine.Equation (ModularCurve.toricPoint F q (c : F)).1
      (ModularCurve.toricPoint F q (c : F)).2 := hns.left

  have hker := ModularCurve.isCyclicKernel_tateBase_prod_X_sub_C_toricPoint_fst F ℓ hℓ2 (c : F) hc q
  have hroot : ((ModularCurve.tateBase F q).preΨ ℓ).eval (ModularCurve.toricPoint F q (c : F)).1 = 0 := by
    obtain ⟨g, hg⟩ := hker.dvd_preΨ
    rw [hg, Polynomial.eval_mul]
    have h1 : (1 : ℕ) ∈ Finset.Icc 1 ((ℓ - 1) / 2) := by
      rw [Finset.mem_Icc]; omega
    rw [Polynomial.eval_prod, Finset.prod_eq_zero h1 (by simp [pow_one]), zero_mul]
  rw [ModularCurve.tateToricPoint_eq_toricPoint]
  exact ⟨heq, hroot, rfl, rfl⟩

end S_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot
end P2MW
export P2MW.S_ModularCurve_isGamma1Point_tateBase_tateToricPoint_of_isPrimitiveRoot (solution)
