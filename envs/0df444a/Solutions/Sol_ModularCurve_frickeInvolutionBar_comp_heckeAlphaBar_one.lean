-- Prove2me | solution 1 for ModularCurve.frickeInvolutionBar_comp_heckeAlphaBar_one
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/d92544d3-002b-5b12-b9db-ada475356bf3

import Mathlib
import Definitions.Def_ModularCurve_HeckeOperator
import Definitions.Def_ModularCurve_CuspidalClass
import Definitions.Def_ModularCurve_AtkinLehnerPartial
import Theorems.Thm_ModularCurve_geomAut_atkinLehner_comp_legs
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 3200000

open AlgebraicCurve ModularCurve

namespace Ws14Fricke

theorem isAtkinLehnerAutFull_one_of_isFrickeAutFull (q : ℕ) [NeZero q]
    {σ : modularFunctionFieldFull (1 * q) ≃ₐ[ℚ] modularFunctionFieldFull (1 * q)}
    (hσ : IsFrickeAutFull (1 * q) σ) : IsAtkinLehnerAutFull 1 q σ := by
  intro d _ hd
  obtain rfl : d = 1 := Nat.dvd_one.mp hd
  exact ⟨hσ 1 (1 * q) (one_mul _) inferInstance inferInstance,
    hσ (1 * q) 1 (mul_one _) inferInstance inferInstance⟩

theorem isAtkinLehnerAutFull_one_frickeInvolutionFull (q : ℕ) [NeZero q] :
    IsAtkinLehnerAutFull 1 q (frickeInvolutionFull (1 * q)) :=
  isAtkinLehnerAutFull_one_of_isFrickeAutFull q
    (isFrickeAutFull_frickeInvolutionFull (1 * q) (exists_isFrickeAutFull_of_neZero (1 * q)))
end Ws14Fricke

theorem solution (q : ℕ) [NeZero q] :
    (frickeInvolutionBar (1 * q)).toAlgHom.comp (heckeAlphaBar (AlgebraicClosure ℚ) 1 q)
      = heckeBetaBar (AlgebraicClosure ℚ) 1 q :=
  (geomAut_atkinLehner_comp_legs (AlgebraicClosure ℚ) 1 q (frickeInvolutionFull (1 * q))
    (Ws14Fricke.isAtkinLehnerAutFull_one_frickeInvolutionFull q)).1

end S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one
end P2MW
export P2MW.S_ModularCurve_frickeInvolutionBar_comp_heckeAlphaBar_one (solution)
