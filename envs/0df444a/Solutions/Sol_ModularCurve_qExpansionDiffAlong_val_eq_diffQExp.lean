-- Prove2me | solution 1 for ModularCurve.qExpansionDiffAlong_val_eq_diffQExp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/9458632c-9138-562a-a9eb-af821df9b204

import Definitions.Def_ModularCurve_QExpansionDiff
import Definitions.Def_ModularCurve_HeckeDifferential
import Theorems.Thm_ModularCurve_theta_coeff
import Theorems.Thm_ModularCurve_eq_qExpansionDiffAlong_of_isQExpansionDiffAlong
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
p2m_attr_erase "simp" "ModularCurve.coe_towerInclBar ModularCurve.coe_towerSubstBar ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

p2m_open "KaehlerDifferential ModularCurve P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve"

section Engine

private theorem qEuler_eq_thetaL {L : Type*} [Field L] (f : LaurentSeries L) :
    qEuler L f = thetaL L f := by
  ext n
  rw [qEuler_coeff, thetaL_apply, theta_coeff, zsmul_eq_mul]

private theorem isQExpansionDiffAlong_restrictScalars {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) :
    IsQExpansionDiffAlong F.val ((diffQExp F).restrictScalars L) := by
  refine ⟨fun x => ?_, fun f ω => ?_⟩
  · show diffQExp F (D L F x) = thetaL L (F.val x)
    rw [diffQExp_D, qEuler_eq_thetaL]
    rfl
  · exact (diffQExp F).map_smul f ω

end Engine

namespace ModularCurve p2m_export "ModularCurve" "thetaL thetaL_apply IsQExpansionDiffAlong qExpansionDiffAlong qEuler qEuler_coeff diffQExp diffQExp_D diffQExpBar modularFunctionFieldBar theta_coeff eq_qExpansionDiffAlong_of_isQExpansionDiffAlong" end ModularCurve
p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExp {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω := by
  have h := eq_qExpansionDiffAlong_of_isQExpansionDiffAlong F.val
    (isQExpansionDiffAlong_restrictScalars F)
  exact (DFunLike.congr_fun h ω).symm

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.qExpansionDiffAlong_val_eq_diffQExpBar (N : ℕ) [NeZero N]
    (ω : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ]) :
    qExpansionDiffAlong (modularFunctionFieldBar N).val ω = diffQExpBar N ω :=
  qExpansionDiffAlong_val_eq_diffQExp (modularFunctionFieldBar N) ω

p2m_open_scoped "ModularCurve" in

private theorem ModularCurve.restrictScalars_diffQExpBar_eq_qExpansionDiffAlong (N : ℕ) [NeZero N] :
    (diffQExpBar N).restrictScalars (AlgebraicClosure ℚ) =
      qExpansionDiffAlong (modularFunctionFieldBar N).val :=
  LinearMap.ext fun ω => (qExpansionDiffAlong_val_eq_diffQExpBar N ω).symm

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp.ModularCurve in

theorem solution {L : Type*} [Field L]
    (F : IntermediateField L (LaurentSeries L)) (ω : Ω[F⁄L]) :
    qExpansionDiffAlong F.val ω = diffQExp F ω :=
  ModularCurve.qExpansionDiffAlong_val_eq_diffQExp F ω

#print axioms solution

end S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp
end P2MW
export P2MW.S_ModularCurve_qExpansionDiffAlong_val_eq_diffQExp (solution)
