-- Prove2me | solution 1 for ModularCurve.LevelRelabelling.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/5d2c8210-560d-57c8-9f25-b434de8a3fc5

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_LevelRelabelling
import Definitions.Def_EllipticCurve_WeilPairingFun
import Theorems.Thm_ModularCurve_IsLevelPStructure_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_LevelRelabelling_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

universe u

open ModularCurve ModularCurve.LevelRelabelling WeierstrassCurve.Affine
open scoped MatrixGroups

theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] [DecidableEq K]
    (W : WeierstrassCurve K) [W.IsElliptic]
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ3 : 3 ≤ ℓ) (hℓK : (ℓ : K) ≠ 0)
    (D : ModularCurve.LevelPData K) (hD : ModularCurve.IsLevelPStructure W ℓ D)
    (C : WeierstrassCurve.VariableChange K) (hCW : C • W = W) (hCD : D.variableChange C = D) :
    C = 1 :=
  ModularCurve.IsLevelPStructure.variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_prime
    ℓ hℓ3 (isUnit_iff_ne_zero.mpr hℓK) W W.isUnit_Δ D hD C hCW hCD

end S_ModularCurve_LevelRelabelling_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure
end P2MW
export P2MW.S_ModularCurve_LevelRelabelling_variableChange_eq_one_of_smul_eq_of_variableChange_eq_of_isLevelPStructure (solution)
