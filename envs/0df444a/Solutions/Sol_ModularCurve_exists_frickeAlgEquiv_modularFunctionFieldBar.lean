-- Prove2me | solution 1 for ModularCurve.exists_frickeAlgEquiv_modularFunctionFieldBar
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.007995+00:00
-- url     : https://prove2.me/submissions/5740db39-aba5-51ce-b7a1-8f7a8f3b1daa

import Mathlib
import Definitions.Def_ModularCurve_ArithmeticGalois
import Definitions.Def_ModularCurve_CuspidalClass
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

open AlgebraicCurve ModularCurve

theorem solution (N : ℕ) [NeZero N] :
    ∃ σ : modularFunctionFieldBar N ≃ₐ[AlgebraicClosure ℚ] modularFunctionFieldBar N,
      ∀ (a b : ℕ) [NeZero a] [NeZero b], a * b = N →
        ∀ x : modularFunctionFieldBar N,
          (x : LaurentSeries (AlgebraicClosure ℚ)) = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq) →
            ((σ x : modularFunctionFieldBar N) : LaurentSeries (AlgebraicClosure ℚ))
              = coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ b jq) := by
  have h : IsFrickeAutFull N (frickeInvolutionFull N) :=
    isFrickeAutFull_frickeInvolutionFull N (ModularCurve.exists_isFrickeAutFull_of_neZero N)
  refine ⟨frickeInvolutionBar N, fun a b _ _ hab x hx => ?_⟩
  have hx' : x = ⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ a jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full N (Dvd.intro b hab))⟩ :=
    Subtype.ext hx
  rw [hx', ModularCurve.frickeInvolutionBar_coeffEmb_qExpand N h a b hab]

end S_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar
end P2MW
export P2MW.S_ModularCurve_exists_frickeAlgEquiv_modularFunctionFieldBar (solution)
