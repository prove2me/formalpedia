-- Prove2me | solution 1 for ModularCurve.ModularPolynomialData.fibrePoly_j_eq_prod_veluQuotient2_j
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/fd18abbd-1f75-54ba-9b7b-46a7c3fa6e05

import Mathlib
import Definitions.Def_ModularCurve_X0
import Definitions.Def_ModularCurve_FibrePoly
import Definitions.Def_ModularCurve_ClassicalModularPolynomials
import Definitions.Def_WeierstrassCurve_Velu
import Definitions.Def_WeierstrassCurve_VeluOrderTwo
import Theorems.Thm_ModularCurve_ModularPolynomialData_phi_eq_phiTwo
import Theorems.Thm_ModularCurve_fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA WeierstrassCurve.VeluQuotientJGates.instIsElliptic27a4"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularCurve.coeffEmb_coeff ModularCurve.coeffMap_coeff ModularCurve.coeffMap_id ModularCurve.coeffMap_single ModularCurve.jqNModC_one ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL WeierstrassCurve.veluX_empty"

set_option autoImplicit false

open Polynomial ModularCurve WeierstrassCurve WeierstrassCurve.Affine

theorem solution
    {K : Type*} [Field K] [IsAlgClosed K] [DecidableEq K] (h2 : (2 : K) ≠ 0)
    (data : ModularPolynomialData 2) (W : WeierstrassCurve K) [W.IsElliptic]
    {ι : Type*} [Fintype ι] (hι : Fintype.card ι = 3) (P : ι → K × K) (hP : Function.Injective P)
    (hPeq : ∀ i, W.toAffine.Equation (P i).1 (P i).2) (hPgy : ∀ i, W.veluGy (P i).1 (P i).2 = 0)
    (hΔ : ∀ i, (W.veluQuotient2 (P i).1 (P i).2).Δ ≠ 0) :
    fibrePoly data.Φ W.j =
      ∏ i, (X - C (@WeierstrassCurve.j K _ (W.veluQuotient2 (P i).1 (P i).2)
        ⟨isUnit_iff_ne_zero.mpr (hΔ i)⟩)) := by
  rw [ModularCurve.ModularPolynomialData.phi_eq_phiTwo data]
  exact ModularCurve.fibrePoly_phiTwo_j_eq_prod_veluQuotient2_j h2 W hι P hP hPeq hPgy hΔ

end S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j
end P2MW
export P2MW.S_ModularCurve_ModularPolynomialData_fibrePoly_j_eq_prod_veluQuotient2_j (solution)
