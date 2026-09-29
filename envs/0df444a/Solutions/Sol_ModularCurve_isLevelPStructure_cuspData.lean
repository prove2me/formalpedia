-- Prove2me | solution 1 for ModularCurve.isLevelPStructure_cuspData
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/0be5c49e-f768-57f1-b103-c9ef6a999d1e

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps
import Theorems.Thm_ModularCurve_equation_tateBase_cuspPoint
import Theorems.Thm_ModularCurve_eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le
import Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_isLevelPStructure_cuspData
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly instDecEqAlgebraicClosureRat WeierstrassCurve.Affine.Point.instDistribMulActionAlgEquiv WeierstrassCurve.Affine.Point.instModuleZModTorsionBy WeierstrassCurve.Affine.Point.instSMulTorsionBy WeierstrassCurve.Affine.Point.instDistribMulActionTorsionBy WeierstrassCurve.Affine.Point.instSMulAlgEquiv"
p2m_attr_erase "simp" "TateCurve.curve_a₂ TateCurve.b_one TateCurve.curve_a₁ TateCurve.term_zero TateCurve.curve_a₆ TateCurve.curve_a₄ TateCurve.curve_a₃ TateCurve.yfun_zero TateCurve.xfun_zero TateCurve.yTerm_zero TateCurve.xTerm_zero TateCurve.xCoeffFull_succ TateCurve.a₆Coeff_zero TateCurve.a₄Coeff_succ TateCurve.a₄Coeff_zero TateCurve.cauchyMul_zero TateCurve.a₆Coeff_succ TateCurve.yCoeffFull_succ TateCurve.xCoeffFull_zero TateCurve.yCoeffFull_zero TateCurve.cauchyMulInt_zero TateCurve.cauchyMulInt3_zero TateCurve.tent_one TateCurve.Gz_zero TateCurve.cauchyMulInt_one TateCurve.tent_zero TateCurve.Fz_zero FLT.DivisorConvolution.sigma_zero_right FLT.DivisorConvolution.sigma_one_right FLT.DivisorConvolution.sigmaConv_one FLT.DivisorConvolution.sigmaConv_zero WeierstrassCurve.Affine.Point.netCol_one WeierstrassCurve.Affine.Point.xOrZero_zero WeierstrassCurve.Affine.Point.netPairing_zero_right WeierstrassCurve.Affine.Point.netW20_some WeierstrassCurve.Affine.Point.netCol_zero WeierstrassCurve.Affine.Point.netPairing_zero_left WeierstrassCurve.Affine.Point.xOrZero_some WeierstrassCurve.Affine.Point.netW20_zero compl₂EDSAux_neg_two"
p2m_attr_erase "simp" "compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two TateCurve.tateTorsionPoint_zero_zero WeierstrassCurve.Universal.halveX_zero WeierstrassCurve.Universal.specialize_X_one WeierstrassCurve.Universal.coeff_halve WeierstrassCurve.Universal.specialize_X_two WeierstrassCurve.Universal.halveCoeff_zero WeierstrassCurve.Universal.specialize_X_four WeierstrassCurve.Universal.coeff_halveX"
p2m_attr_erase "simp" "WeierstrassCurve.Universal.specialize_X_three WeierstrassCurve.Universal.specialize_X_zero"

set_option autoImplicit false

universe u

open ModularCurve

theorem solution {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0)
    (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ v w) := by
  have hv : v ≠ 0 := by rintro rfl; apply hvw; simp
  have hw : w ≠ 0 := by rintro rfl; apply hvw; simp
  have hwv : w 0 * v 1 - w 1 * v 0 ≠ 0 := by
    intro h; apply hvw; linear_combination -h
  exact
    { equation_P := by
        rw [cuspData_xP, cuspData_yP]; exact ModularCurve.equation_tateBase_cuspPoint hp ζ hζ v hv
      equation_Q := by
        rw [cuspData_xQ, cuspData_yQ]; exact ModularCurve.equation_tateBase_cuspPoint hp ζ hζ w hw
      preΨ_P := by
        rw [cuspData_xP]
        exact ModularCurve.eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le hp5 hp ζ hζ v hv
      preΨ_Q := by
        rw [cuspData_xQ]
        exact ModularCurve.eval_prePsi_tateBase_cuspPoint_eq_zero_of_five_le hp5 hp ζ hζ w hw
      isUnit_indepElt_PQ := by
        rw [cuspData_xP, cuspData_xQ]
        exact ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le hp5 hp ζ hζ v w hvw
      isUnit_indepElt_QP := by
        rw [cuspData_xP, cuspData_xQ]
        exact ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le hp5 hp ζ hζ w v hwv }

end S_ModularCurve_isLevelPStructure_cuspData
end P2MW
export P2MW.S_ModularCurve_isLevelPStructure_cuspData (solution)
