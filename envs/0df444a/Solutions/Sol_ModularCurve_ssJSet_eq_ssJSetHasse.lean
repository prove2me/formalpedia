-- Prove2me | solution 1 for ModularCurve.ssJSet_eq_ssJSetHasse
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.620212+00:00
-- url     : https://prove2.me/submissions/6b095d68-6da6-5bb2-9f13-3ea86de6f89b

import Mathlib
import Definitions.Def_ModularCurve_SupersingularModuli
import Definitions.Def_WeierstrassCurve_HasseInvariant
import Theorems.Thm_WeierstrassCurve_forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse
p2m_attr_erase "instance" "WeierstrassCurve.instIsEllipticBaseChange WeierstrassCurve.Univ.Affine.instAddGroupPointFieldBaseChangeMvPolynomialCoeffIntCurve WeierstrassCurve.Univ.instIsEllipticFieldPointedCurve WeierstrassCurve.Univ.instCommRingPoly"
p2m_attr_erase "simp" "compl₂EDSAux_neg_two compl₂EDSAux_zero WeierstrassCurve.ωe_zero WeierstrassCurve.Univ.pointedCurve_a₁ WeierstrassCurve.Univ.polyToField_polynomial WeierstrassCurve.Coeff.A₁.sizeOf_spec compl₂EDS_zero compl₂EDS_one WeierstrassCurve.Univ.Affine.smulY_zero Param.C.sizeOf_spec EllSequence.redInvarDenom_zero compl₂EDSAux_two compl₂EDSAux_neg_one compl₂EDSAux_one WeierstrassCurve.Coeff.A₆.sizeOf_spec WeierstrassCurve.ψc_neg WeierstrassCurve.Univ.Affine.smulY_one WeierstrassCurve.Univ.Affine.smulX_one WeierstrassCurve.Coeff.A₂.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₄ compl₂EDS_neg WeierstrassCurve.Univ.pointedCurve_a₃ EllSequence.redInvarDenom_two WeierstrassCurve.Univ.pointedCurve_a₆ Param.D.sizeOf_spec WeierstrassCurve.ωe_one WeierstrassCurve.Univ.Affine.smulX_zero WeierstrassCurve.Coeff.A₃.sizeOf_spec EllSequence.redInvarDenom_one WeierstrassCurve.Coeff.A₄.sizeOf_spec WeierstrassCurve.Univ.pointedCurve_a₂ Param.B.sizeOf_spec compl₂EDS_two"

set_option autoImplicit false

open ModularCurve

theorem solution (q : ℕ) [Fact q.Prime] (hq : q ≠ 2)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K q] [DecidableEq K] :
    ssJSet q K = ssJSetHasse q K := by
  ext j
  simp only [ModularCurve.ssJSet, ModularCurve.ssJSetHasse, Set.mem_setOf_eq]
  constructor
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mp (h W hj)
  · intro h W _ hj
    exact (W.forall_nsmul_eq_zero_iff_hasseInvariant_eq_zero q hq).mpr (h W hj)

end S_ModularCurve_ssJSet_eq_ssJSetHasse
end P2MW
export P2MW.S_ModularCurve_ssJSet_eq_ssJSetHasse (solution)
