-- Prove2me | solution 1 for ModularCurve.MultCovering.frickeInvolutionBar_jF
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:10.583295+00:00
-- url     : https://prove2.me/submissions/afe01ab2-fa30-5ab3-95cc-962ccbc676e2

import Mathlib
import Definitions.Def_ModularCurve_MultCoveringCharts
import Theorems.Thm_ModularCurve_frickeInvolutionBar_coeffEmb_qExpand
import Theorems.Thm_ModularCurve_exists_isFrickeAutFull_of_neZero
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_MultCovering_frickeInvolutionBar_jF
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 1600000
set_option autoImplicit false

p2m_open "ModularCurve P2MW.S_ModularCurve_MultCovering_frickeInvolutionBar_jF.ModularCurve ModularCurve.MultCovering P2MW.S_ModularCurve_MultCovering_frickeInvolutionBar_jF.ModularCurve.MultCovering"

namespace ModularCurve
p2m_export "ModularCurve" "IsFrickeAutFull frickeInvolutionFull isFrickeAutFull_frickeInvolutionFull qExpand qExpand_one_apply jq jqd_mem_full modularFunctionFieldBar coeffEmb coeffEmb_mem_laurentBaseChange frickeInvolutionBar frickeInvolutionBar_coeffEmb_qExpand exists_isFrickeAutFull_of_neZero"
namespace MultCovering
p2m_export "ModularCurve.MultCovering" "jF jpF"
namespace P2MzF
p2m_open "ModularCurve.MultCovering ModularCurve"
theorem isFrickeAutFull_oneMul (p : ℕ) [Fact p.Prime] :
    IsFrickeAutFull (1 * p) (frickeInvolutionFull (1 * p)) :=
  isFrickeAutFull_frickeInvolutionFull (1 * p) (exists_isFrickeAutFull_of_neZero (1 * p))
end ModularCurve.MultCovering.P2MzF

open ModularCurve.MultCovering.P2MzF

theorem solution (p : ℕ) [Fact p.Prime] : frickeInvolutionBar (1 * p) (jF p) = jpF p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h := frickeInvolutionBar_coeffEmb_qExpand (1 * p) (isFrickeAutFull_oneMul p) 1 p rfl
  have e1 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ 1 jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro p rfl))⟩ :
        modularFunctionFieldBar (1 * p)) = jF p := Subtype.ext (by simp only [qExpand_one_apply])
  have e2 : (⟨coeffEmb (AlgebraicClosure ℚ) (qExpand ℚ p jq),
      coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqd_mem_full (1 * p) (Dvd.intro_left 1 rfl))⟩ :
        modularFunctionFieldBar (1 * p)) = jpF p := Subtype.ext rfl
  rw [e1, e2] at h
  exact h

end S_ModularCurve_MultCovering_frickeInvolutionBar_jF
end P2MW
export P2MW.S_ModularCurve_MultCovering_frickeInvolutionBar_jF (solution)
