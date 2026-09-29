-- Prove2me | solution 1 for ModularCurve.inertiaDegAlong_eq_one_laurentBaseChange
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:12.280726+00:00
-- url     : https://prove2.me/submissions/4d12ec48-c490-51d8-a10c-8b512883c6e0

import Definitions.Def_ModularCurve_HeckeOperator
import Theorems.Thm_ModularCurve_modularFunctionField_eq_full
import Theorems.Thm_ModularCurve_laurentBaseChange_modularFunctionField
import Theorems.Thm_ModularCurve_place_deg_eq_one_of_isAlgClosed
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
p2m_attr_erase "instance" "ModularCurve.PhiGen.instNeZeroPhiGenCosetA"
p2m_attr_erase "simp" "ModularCurve.evalAtJqN_X ModularCurve.qTwistFun_coeff ModularCurve.swapBivar_C_X ModularCurve.PhiGen.cosetA_succ ModularCurve.qTwist_coeff ModularCurve.PhiGen.cosetB_zero ModularCurve.PhiGen.cosetA_zero ModularCurve.qTwist_single ModularCurve.swapBivar_X ModularCurve.aeval_toRingHom_X ModularCurve.PhiGen.cosetB_succ ModularForm.val_heckeDiagMatrix ModularForm.heckeU_zero ModularForm.heckeU_zero_left ModularForm.heckeT_zero ModularForm.val_heckeMatrix ModularForm.heckeMatrix_zero ModularForm.heckeT_zero_left ModularForm.heckeDiagMatrix_zero ModularForm.val_upperTriangularGL"

set_option autoImplicit false

namespace AlgebraicCurve
p2m_export "AlgebraicCurve" "algebraAlong isScalarTower_along isIntegral_along Place"
p2m_open "AlgebraicCurve"

variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']

namespace Place p2m_export "AlgebraicCurve.Place" "inertiaDegAlong restrict inertiaDeg deg_restrict_mul_inertiaDeg deg" end Place
namespace Place
p2m_open_scoped "AlgebraicCurve.Place" in

private theorem _root_.AlgebraicCurve.Place.inertiaDegAlong_eq_one_of_deg_target_eq_one (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral)
    (w : Place K F') (hw : w.deg = 1) : w.inertiaDegAlong φ hφ = 1 := by
  letI := algebraAlong φ
  haveI := isScalarTower_along φ
  haveI := isIntegral_along φ hφ
  have h : (w.restrict F).deg * w.inertiaDeg F = 1 := hw ▸ w.deg_restrict_mul_inertiaDeg

  exact Nat.eq_one_of_mul_eq_one_left h

end Place
p2m_export "AlgebraicCurve" "Place.inertiaDegAlong_eq_one_of_deg_target_eq_one"
end AlgebraicCurve

namespace ModularCurve
p2m_export "ModularCurve" "modularFunctionFieldFull laurentBaseChange modularFunctionField_eq_full laurentBaseChange_modularFunctionField modularFunctionFieldC place_deg_eq_one_of_isAlgClosed"
p2m_open "ModularCurve"

p2m_open "AlgebraicCurve P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange.AlgebraicCurve"

variable (L : Type*) [Field L] [Algebra ℚ L] (N : ℕ)

private theorem laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldC [NeZero N] :
    laurentBaseChange L (modularFunctionFieldFull N) = modularFunctionFieldC L N := by
  rw [← modularFunctionField_eq_full, laurentBaseChange_modularFunctionField]

private theorem deg_eq_one_laurentBaseChange [NeZero N] [IsAlgClosed L]
    (W : Place L (laurentBaseChange L (modularFunctionFieldFull N))) : W.deg = 1 := by
  revert W
  rw [laurentBaseChange_modularFunctionFieldFull_eq_modularFunctionFieldC]
  exact place_deg_eq_one_of_isAlgClosed L N

theorem _root_.P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange.solution {L : Type*} [Field L] [Algebra ℚ L]
    [IsAlgClosed L] {N M : ℕ} [NeZero M]
    (φ : laurentBaseChange L (modularFunctionFieldFull N) →ₐ[L]
      laurentBaseChange L (modularFunctionFieldFull M))
    (hφ : φ.toRingHom.IsIntegral)
    (W : Place L (laurentBaseChange L (modularFunctionFieldFull M))) :
    W.inertiaDegAlong φ hφ = 1 :=
  W.inertiaDegAlong_eq_one_of_deg_target_eq_one φ hφ (deg_eq_one_laurentBaseChange L M W)

end ModularCurve

end S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange
end P2MW
export P2MW.S_ModularCurve_inertiaDegAlong_eq_one_laurentBaseChange (solution)
